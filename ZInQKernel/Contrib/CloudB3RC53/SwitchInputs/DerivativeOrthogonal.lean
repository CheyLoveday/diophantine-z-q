import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.FibreDualityWiring
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthPlaces

/-!
# RC53 SwitchInputs: the local complement criterion `horth` for the derivative pair

Proposition `ex:limits-uniform-lower-bound`, height-one regularity, the switch at a derivative
place (tex L5055–5086), "The retained localization-duality diagrams give `U = U^⊥`" (tex
L5062–5070, Nekovář 6.3.3–6.3.4); Nekovář, *Selmer complexes* (Astérisque 310, 2006), 6.2.7
(orthogonal complements are defined place by place: `Δ(X₁) ⊥⊥ Δ(X₂)` iff `Δ_v(X₁) ⊥⊥ Δ_v(X₂)` for
every `v`).

`FibreDualityWiring.lean` leaves the hypothesis `horth`
(`FibreOrthogonalComplementsT β … ΔS ΔR I tr htr`) open for the switch `galRelSwitch C c q T`:
strict conditions `ΔS = switchStrK q (old c)` against relaxed conditions `ΔR = switchRelK q (old c)`,
through a self-pairing `β : M × M → T`. This file reduces it to the places.

**(1) The per-place reduction** (PROVED, from lane RC29's splitting lemma
`orth_localDualityMapT_quasiIso`): `fibreSwitch_horth_of_places` (any RC31 `FibreSwitch`) and
`galRelSwitch_horth_of_places` (the chain's switch). For finitely many places, local traces `tr_v`
killing coboundaries, a global trace whose local part is `∑_v tr_v` (`hsum`; RC31's
`FibreLocalTraces.Normalizes`), and any `τ≥2` isotropy data `I` (they are given place by place:
`I.h v`), `horth` holds as soon as the per-place local duality maps
`Cone(U_v → C(G_v, M))[−1] → Hom_k(U'_v, k)[−3]`, `(u, x) ↦ (y ↦ tr_v(x ∪ i'_v y + h_v(u, y)))`
(`switchPlaceMap`) are quasi-isomorphisms:
* at the switch place `q` (`hq`): strict `τ≤0 = [Z⁰ → 0]` against relaxed `τ≤1 = [C⁰ → Z¹]`;
* at every other place `v ≠ q` (`hold`): the old condition `old c v` against ITSELF (at `v ≠ q`
  both `switchStrK q (old c) v` and `switchRelK q (old c) v` are `old c v`). This is
  per-place self-orthogonality of the old conditions; it is an explicit hypothesis. The
  configuration conditions `SwitchCondsK.A₀`, `Ad` are arbitrary subcomplexes away from a switch
  place, so `hold` is not provable for the chain as stated; see (3) for the standard conditions.

**(3) Finding: the singular side at a characteristic-zero fibre is not self-orthogonal.** For the
standard conditions (`PlaceTameK.std`: `finCond = sideOfSetK I_v`, `singCond = sideOfSetK {φ_v}`)
`hold` asks the finite side, resp. the singular side, to be its own orthogonal complement at each
place outside `c`, resp. in `c`. On homology a self-orthogonal condition `U ⊆ τ≤1` (with
`H⁰(U) = H⁰(G_v, M)`) has `H¹(U)` equal to its own annihilator in `H¹(G_v, M)` under local duality,
so `2 · dim H¹(U) = dim H¹(G_v, M)`.
* In the derivative model at an inert derivative place over a characteristic-zero fibre
  (`Φ = J² = 1`, `q = ℓ² ≠ 1` in `k(𝔭)`) the singular part vanishes
  (`UnrCoords.singular_zero_of_q_ne_one`): `H¹` of the singular side is `0`, while
  `H¹(G_v, M) ≅ coker(Φ − 1) = M ≠ 0` (`UnrCoords.finrank_H1WrelK_of_q_ne_one`). So the singular
  side is NOT self-orthogonal there, and `hold` FAILS for the standard conditions whenever such a
  place carries the singular side.
* In the same model the fibre duality itself has no input: an equivariant self-pairing into a
  twist on which the Frobenius acts by `q` is zero unless `q = 1` when the Frobenius acts trivially
  on `M` (`selfPairing_zero_of_trivial_action`, PROVED below). So the derivative model and the
  perfect self-pairing `β` of RC31's duality are jointly satisfiable only when `q = 1`.
* For the genuine `V_𝔭` at a good inert `ℓ` the Frobenius is not trivial and (Weil bounds) has
  neither `1` nor `q` as an eigenvalue, so `H¹(G_v, V_𝔭) = 0`: every condition is self-orthogonal on
  homology, but there are no `2 + 2` coordinates and the switch step is empty.
This is the constraint of the `2 + 2` shape again (`UnrCoords.two_plus_two_iff_q_eq_one`): Elliot's
isotropic planes `F`, `S` exist only when `q ≡ 1`, i.e. in the inner limit `ℓᵢ → −1` (tex
L5033–5035), and the switch has to be formalised on inner-limit objects. The finite side (cocycles
vanishing on inertia; the unramified condition) is self-orthogonal at places not above `2` where
`M` is unramified (Nekovář 7.5.6; lane RC29's PRINT `NekovarProp756`, for discrete coefficients);
RC31 has no such print for the fibres. (Homological argument recorded, not formalised, except
`selfPairing_zero_of_trivial_action`.)

Kinds: definitions and PROVED (from the hypotheses named in each statement).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Manuscript.RC.SelmerComplex NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.FibreDuality (FibreSwitch GalTruncIsotropyData galCompactTT galPairDataT
  FibreOrthogonalComplementsT FibreLocalTraces)
open ZInQ.Manuscript.RC.KummerMaps (orthLocalMap orthNeg orthPlaceMap orth_localDualityMapT_quasiIso)

/-! ### (1) The per-place reduction -/

section Reduction

variable {k : Type} [Field k] {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  {M T : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : M × M => β x.1 x.2)

/-- **The per-place local duality map of a fibre switch** (Nekovář 6.2.2, `u⁻_{π,h_v}`): at the
place `v`, `Cone(U_str,v → C(G_v, M))[−1] → Hom_k(U_rel,v, k)[−3]`,
`(u, x) ↦ (y ↦ tr_v(x ∪ i_v y + h_v(u, y)))` (lane RC29's `orthPlaceMap` for `(ΔS, ΔR)`). -/
abbrev switchPlaceMap (X : FibreSwitch K S k M) (I : GalTruncIsotropyData S k β hβ hβc X.ΔS X.ΔR)
    (trv : ∀ v : Places K S, (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[k] k)
    (htrv : ∀ v z, trv v ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0) (v : Places K S) :=
  orthPlaceMap k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ hβc
    X.ΔS X.ΔR I trv htrv v

/-- **`horth` for a fibre switch, place by place** (Nekovář 6.2.7; tex L5062–5070): for finitely
many places, local traces `tr_v` killing coboundaries, a global trace on the truncated compact cone
whose local part is `∑_v tr_v` (`hsum`) and any `τ≥2` isotropy data `I`, the strict and relaxed
conditions of the switch are orthogonal complements once the per-place local duality map is a
quasi-isomorphism at the switch place `q` (`hq`) and at every other place (`hold`).
Classification: PROVED (lane RC29's `orth_localDualityMapT_quasiIso`). -/
theorem fibreSwitch_horth_of_places [Fintype (Places K S)] (X : FibreSwitch K S k M)
    (I : GalTruncIsotropyData S k β hβ hβc X.ΔS X.ΔR)
    (trv : ∀ v : Places K S, (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[k] k)
    (htrv : ∀ v z, trv v ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0)
    (tr : (galCompactTT S k β hβ hβc X.ΔS X.ΔR I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galCompactTT S k β hβ hβc X.ΔS X.ΔR I).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1),
      tr ((0 : (globalCx k (GKS K S) T).X 3), (truncSub (localSumCx k (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v))
    (q : Places K S)
    (hq : QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc X I trv htrv q)))
    (hold : ∀ v, v ≠ q → QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc X I trv htrv v))) :
    FibreOrthogonalComplementsT β hβ hβc X.ΔS X.ΔR I tr htr :=
  orth_localDualityMapT_quasiIso k (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) β hβ hβc X.ΔS X.ΔR I trv htrv tr htr hsum (fun v => by
      by_cases h : v = q
      · subst h
        exact hq
      · exact hold v h)

/-- **`horth` for a fibre switch from RC31's trace packet, place by place**: as
`fibreSwitch_horth_of_places`, with the local traces of one packet `L : FibreLocalTraces` and a
global trace normalized by it (`L.Normalizes tr`, RC31's form of `hsum`). Classification: PROVED. -/
theorem fibreSwitch_horth_of_packet [Fintype (Places K S)] (X : FibreSwitch K S k M)
    (I : GalTruncIsotropyData S k β hβ hβc X.ΔS X.ΔR) (L : FibreLocalTraces S k T)
    (tr : (galCompactTT S k β hβ hβc X.ΔS X.ΔR I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galCompactTT S k β hβ hβc X.ΔS X.ΔR I).d 2 3 rfl z) = 0)
    (hsum : L.Normalizes tr) (q : Places K S)
    (hq : QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc X I L.trv (fun v z => L.htrv v z) q)))
    (hold : ∀ v, v ≠ q →
      QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc X I L.trv (fun v z => L.htrv v z) v))) :
    FibreOrthogonalComplementsT β hβ hβc X.ΔS X.ΔR I tr htr :=
  fibreSwitch_horth_of_places β hβ hβc X I L.trv (fun v z => L.htrv v z) tr htr hsum q hq hold

variable (C : SwitchCondsK k K S M) (c : Finset (Places K S)) (q : Places K S)
  (Tq : TameCoordinatesTrivialK k (gMvK K S M q) (C.D.I q) (C.D.φ q) (C.D.σ q))

/-- **`horth` for the chain's switch, place by place** (tex L5055–5086 with Nekovář 6.2.7): for
`galRelSwitch C c q Tq`, the strict/relaxed derivative conditions at `q` and the old conditions
`old c` elsewhere are orthogonal complements once (at `q`) strict `τ≤0` is orthogonal to relaxed
`τ≤1` and (at `v ≠ q`) each old condition `old c v` is its own orthogonal complement.
Classification: PROVED (from `fibreSwitch_horth_of_places`). -/
theorem galRelSwitch_horth_of_places [Fintype (Places K S)]
    (I : GalTruncIsotropyData S k β hβ hβc (galRelSwitch C c q Tq).ΔS (galRelSwitch C c q Tq).ΔR)
    (trv : ∀ v : Places K S, (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[k] k)
    (htrv : ∀ v z, trv v ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0)
    (tr : (galCompactTT S k β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galCompactTT S k β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR I).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1),
      tr ((0 : (globalCx k (GKS K S) T).X 3), (truncSub (localSumCx k (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v))
    (hq : QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc (galRelSwitch C c q Tq) I trv htrv q)))
    (hold : ∀ v, v ≠ q →
      QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc (galRelSwitch C c q Tq) I trv htrv v))) :
    FibreOrthogonalComplementsT β hβ hβc (galRelSwitch C c q Tq).ΔS (galRelSwitch C c q Tq).ΔR I
      tr htr :=
  fibreSwitch_horth_of_places β hβ hβc (galRelSwitch C c q Tq) I trv htrv tr htr hsum q hq hold

/-- At a place `v ≠ q` the strict condition complex of the chain's switch is the old condition
`old c v` (so the per-place hypothesis `hold` pairs `old c v` with itself). PROVED. -/
theorem galRelSwitch_US_ne {v : Places K S} (hv : v ≠ q) :
    (galRelSwitch C c q Tq).US v = (C.old c v).cx := by
  unfold galRelSwitch
  dsimp only
  rw [switchStrK, ite_eq_right hv]

/-- At a place `v ≠ q` the relaxed condition complex of the chain's switch is the old condition
`old c v`. PROVED. -/
theorem galRelSwitch_UR_ne {v : Places K S} (hv : v ≠ q) :
    (galRelSwitch C c q Tq).ΔR.U v = (C.old c v).cx := by
  unfold galRelSwitch
  dsimp only [galCond]
  rw [switchRelK, ite_eq_right hv]

end Reduction

/-! ### (3) The self-pairing at a place with trivial Frobenius -/

section SelfPairing

variable {k : Type} [Field k] {G M T : Type} [Monoid G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [AddCommGroup T] [Module k T] [DistribMulAction G T]

/-- **An equivariant pairing is zero when an element acting trivially on `M` acts on the target by
a scalar `q ≠ 1`**: `β(a, b) = β(g a, g b) = g β(a, b) = q β(a, b)`. At a derivative place of the
model (`Φ = 1` on `M`, `Φ = q` on `k(𝔭)(1)`, `q = ℓ² ≠ 1` in characteristic zero) there is no
nonzero equivariant self-pairing into the Tate twist, so RC31's perfect `β` and the derivative
model are jointly satisfiable only when `q = 1`. Classification: PROVED. -/
theorem selfPairing_zero_of_trivial_action (β : M →ₗ[k] M →ₗ[k] T)
    (hβ : ∀ (g : G) (a b : M), β (g • a) (g • b) = g • β a b) (g : G) (q : k)
    (hM : ∀ m : M, g • m = m) (hT : ∀ t : T, g • t = q • t) (hq : q ≠ 1) (a b : M) :
    β a b = 0 := by
  have h := hβ g a b
  rw [hM a, hM b, hT] at h
  have h2 : (q - 1) • β a b = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hq)

end SelfPairing

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
