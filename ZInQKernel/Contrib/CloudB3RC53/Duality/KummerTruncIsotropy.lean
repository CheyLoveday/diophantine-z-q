import ZInQKernel.Contrib.CloudB3RC53.Duality.DerivedKummerTrunc
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.TruncIsotropy

/-!
# Duality area: Kummer-condition isotropy into `τ≥2` (tex L3443–3450)

Lemma `ex:arith-local-kummer`, tex L3443–3450, at one place, for the `τ≥2` local target of
Nekovář's construction (*Selmer complexes*, Sections 6.2–6.3; `SwitchInputs/TruncIsotropy.lean`).

**The interface.** `LocalTruncIsotropy ι ι' P` is a small placeholder for the per-place `τ≥2`
isotropy data: local conditions `ι : U → L`, `ι' : U' → L'`, a local cup product
`P : L × L' → E`, a family `h` of degree `−1`, and exactly the two isotropy fields of
`SwitchInputs.SelPairDataTrunc`. Field correspondence (at a place `v`, for genuine conditions
`ΔA`, `ΔB` with local cup product `localPair v`):

| `LocalTruncIsotropy` | `SelPairDataTrunc` (`genuinePairData` pattern) |
|---|---|
| `U`, `U'`, `ι`, `ι'` | `D.U`, `D'.U`, `D.ι`, `D'.ι` at `v` (`ΔA.U v`, `ΔA.i v`, …) |
| `E`, `P` | `EL`, `cupL` at `v` (`localCx T v`, `localPair v`) |
| `h` | `hU` at `v` (`hU i j k _ x y v = h v i j k _ (x v) (y v)`) |
| `isotropy₂` (mod `d(E¹)`) | `isotropy₂` at `v` |
| `isotropy₃` (degrees `≥ 3`) | `isotropy₃` at `v` |

`ofSelPairDataTrunc` and `toSelPairDataTrunc` make the correspondence literal for one `SelData`.

**Results.**
* `pullPair`: the restricted cup product `U × U' → E`, `(u, v) ↦ ι u ∪ ι' v`.
* `ofTruncZero`: if the restricted cup product vanishes after projecting to `τ≥2 E`, the zero family
  is a `τ≥2` isotropy homotopy.
* **`kummerTruncIsotropy` (PROVED, finite level, any coefficient ring)**: for conditions concentrated
  in degrees `0, 1` and a local trace `trv : E² → R` whose kernel on the degree-two cocycles
  consists of coboundaries (the first half of `InducesIsoH2`, `RC/SelmerComplex/Prints.lean`), if
  `trv (ι u ∪ ι' v) = 0` for all `(1, 1)` classes, the zero family is a `τ≥2` isotropy homotopy.
* **`kummerTruncIsotropy_two` (PROVED, `ℤ₂`)**: the same with `trv` killing coboundaries and the
  hypothesis weakened to "every value `trv (ι u ∪ ι' v)` is divisible by every power of two"
  (finite isotropy), via `derivedKummerStep_trunc` applied to `τ≥2 E`.
* `trunc_h_eq_zero`: for such conditions every `τ≥2` isotropy homotopy projects to zero in `τ≥2 E`
  (uniqueness; `nullHomotopy_eq_zero`).
* LESSON 2: `exTruncLocal` (the interface for the derivative conditions of
  `SwitchInputs/TruncIsotropy.lean`, where no untruncated homotopy exists) and `kummerEx` (the Kummer
  hypotheses in an example with a NONZERO `(1, 1)` cup value that is a coboundary).

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Duality

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology (VanishesOutside)

universe u

section Interface

variable {S : Type u} [CommRing S] {U U' L L' E : GCx S}

/-- **The per-place `τ≥2` isotropy interface**: a family `h` of degree `−1` with the two isotropy
fields of `SelPairDataTrunc` — target degree two modulo `d(E¹)` and target degrees `≥ 3` exactly. -/
structure LocalTruncIsotropy (ι : GHom U L) (ι' : GHom U' L') (P : GPair L L' E) where
  /-- The isotropy homotopy, of degree `−1`. -/
  h : ∀ i j k : ℤ, i + j = k + 1 → U.X i →ₗ[S] U'.X j →ₗ[S] E.X k
  /-- Target degree two, modulo the coboundaries `d(E¹)`. -/
  isotropy₂ : ∀ (i i₁ j j₁ : ℤ) (hh : i + j = 2) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (u : U.X i) (v : U'.X j),
    h i₁ j 2 (by omega) (U.d i i₁ hi u) v + sgn i • h i j₁ 2 (by omega) u (U'.d j j₁ hj v) -
        P.P i j 2 hh (ι.f i i rfl u) (ι'.f j j rfl v) ∈ LinearMap.range (E.d 1 2 rfl)
  /-- Target degrees `≥ 3`, exactly. -/
  isotropy₃ : ∀ (i i₁ j j₁ k k₁ : ℤ) (hh : i + j = k + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hk : k + 1 = k₁), 3 ≤ k₁ → ∀ (u : U.X i) (v : U'.X j),
    E.d k k₁ hk (h i j k hh u v) + h i₁ j k₁ (by omega) (U.d i i₁ hi u) v +
        sgn i • h i j₁ k₁ (by omega) u (U'.d j j₁ hj v) =
      P.P i j k₁ (by omega) (ι.f i i rfl u) (ι'.f j j rfl v)

/-- The local data of truncated Selmer pairing data satisfy the interface (field correspondence). -/
def ofSelPairDataTrunc {D D' : SelData S} (Q : SelPairDataTrunc D D') :
    LocalTruncIsotropy D.ι D'.ι Q.cupL :=
  ⟨Q.hU, Q.isotropy₂, Q.isotropy₃⟩

/-- Conversely, the interface for the local data of one `SelData`, with the global target, the
global cup product and the compatibility, gives truncated Selmer pairing data. -/
def LocalTruncIsotropy.toSelPairDataTrunc {D D' : SelData S} {EL : GCx S} {cupL : GPair D.L D'.L EL}
    (J : LocalTruncIsotropy D.ι D'.ι cupL) (E : GCx S) (resE : GHom E EL) (cupG : GPair D.G D'.G E)
    (compat : ∀ (i j k i' j' k' : ℤ) (h : i + j = k) (h' : i' + j' = k') (hi : i = i') (hj : j = j')
      (hk : k = k') (a : D.G.X i) (b : D'.G.X j),
      resE.f k k' hk (cupG.P i j k h a b) =
        cupL.P i' j' k' h' (D.res.f i i' hi a) (D'.res.f j j' hj b)) :
    SelPairDataTrunc D D' :=
  ⟨E, EL, resE, cupG, cupL, compat, J.h, J.isotropy₂, J.isotropy₃⟩

/-- **The restricted cup product** `U × U' → E`, `(u, v) ↦ ι u ∪ ι' v`. -/
def pullPair (P : GPair L L' E) (ι : GHom U L) (ι' : GHom U' L') : GPair U U' E where
  P i j k h := (P.P i j k h).compl₁₂ (ι.f i i rfl) (ι'.f j j rfl)
  leib i i₁ j j₁ k k₁ h hi hj hk x y := by
    change E.d k k₁ hk (P.P i j k h (ι.f i i rfl x) (ι'.f j j rfl y)) =
      P.P i₁ j k₁ _ (ι.f i₁ i₁ rfl (U.d i i₁ hi x)) (ι'.f j j rfl y) +
        sgn i • P.P i j₁ k₁ _ (ι.f i i rfl x) (ι'.f j₁ j₁ rfl (U'.d j j₁ hj y))
    rw [ι.comm i i₁ i i₁ rfl hi hi rfl x, ι'.comm j j₁ j j₁ rfl hj hj rfl y]
    exact P.leib i i₁ j j₁ k k₁ h hi hj hk _ _

theorem pullPair_P (P : GPair L L' E) (ι : GHom U L) (ι' : GHom U' L') (i j k : ℤ) (h : i + j = k)
    (u : U.X i) (v : U'.X j) :
    (pullPair P ι ι').P i j k h u v = P.P i j k h (ι.f i i rfl u) (ι'.f j j rfl v) :=
  rfl

/-- **The zero family is a `τ≥2` isotropy homotopy** as soon as the restricted cup product vanishes
in `τ≥2 E`. -/
def ofTruncZero {ι : GHom U L} {ι' : GHom U' L'} {P : GPair L L' E}
    (hz : ∀ (i j k : ℤ) (h : i + j = k) (u : U.X i) (v : U'.X j),
      (truncPair (pullPair P ι ι')).P i j k h u v = 0) :
    LocalTruncIsotropy ι ι' P where
  h _ _ _ _ := 0
  isotropy₂ i i₁ j j₁ hh hi hj u v := by
    have e := hz i j 2 hh u v
    change (truncSub E 2).mkQ (P.P i j 2 hh (ι.f i i rfl u) (ι'.f j j rfl v)) = 0 at e
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, truncSub_of_eq E rfl] at e
    obtain ⟨y, hy⟩ := e
    refine ⟨-y, ?_⟩
    simp only [LinearMap.zero_apply, smul_zero, add_zero, zero_sub, map_neg, hy]
  isotropy₃ i i₁ j j₁ k k₁ hh hi hj hk h3 u v := by
    have e := hz i j k₁ (by omega) u v
    change (truncSub E k₁).mkQ (P.P i j k₁ _ (ι.f i i rfl u) (ι'.f j j rfl v)) = 0 at e
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, truncSub_of_ge E h3,
      Submodule.mem_bot] at e
    rw [e]
    simp only [LinearMap.zero_apply, map_zero, smul_zero, add_zero]

theorem ofTruncZero_h {ι : GHom U L} {ι' : GHom U' L'} {P : GPair L L' E}
    (hz : ∀ (i j k : ℤ) (h : i + j = k) (u : U.X i) (v : U'.X j),
      (truncPair (pullPair P ι ι')).P i j k h u v = 0) :
    (ofTruncZero hz).h = fun _ _ _ _ => 0 :=
  rfl

/-- `τ≥2 E` vanishes in degrees `≤ 1`. -/
theorem truncGe2_vanishes (E : GCx S) : VanishesOutside (truncGe2 E) (fun k => 2 ≤ k) := by
  intro k hk
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := (truncSub E k).mkQ_surjective a
  obtain ⟨b, rfl⟩ := (truncSub E k).mkQ_surjective b
  change (truncSub E k).mkQ a = (truncSub E k).mkQ b
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    truncSub_of_le E (by omega)]
  trivial

/-- The degree bounds for the restricted cup product into `τ≥2 E`. -/
theorem truncBounds_of (hU : VanishesOutside U (fun i => i = 0 ∨ i = 1))
    (hU' : VanishesOutside U' (fun i => i = 0 ∨ i = 1)) : TruncBounds U U' (truncGe2 E) :=
  ⟨hU, hU', truncGe2_vanishes E⟩

/-- A degree-two element whose class in `τ≥2 E` is a cocycle is a cocycle. -/
theorem cocycle_of_trunc (t : E.X 2) (ht : (truncGe2 E).d 2 3 rfl ((truncSub E 2).mkQ t) = 0) :
    E.d 2 3 rfl t = 0 := by
  rw [truncGe2_d_mk] at ht
  change (truncSub E 3).mkQ (E.d 2 3 rfl t) = 0 at ht
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, truncSub_of_ge E le_rfl,
    Submodule.mem_bot] at ht
  exact ht

variable {ι : GHom U L} {ι' : GHom U' L'} {P : GPair L L' E}

/-- **Kummer-condition isotropy into `τ≥2`, finite level** (tex L3443–3450; PROVED): for conditions
concentrated in degrees `0, 1` and a local trace whose kernel on degree-two cocycles consists of
coboundaries (`InducesIsoH2`, first half), if the trace of every `(1, 1)` cup value
`ι u ∪ ι' v` vanishes, the zero family is a `τ≥2` isotropy homotopy. -/
def kummerTruncIsotropy (hU : VanishesOutside U (fun i => i = 0 ∨ i = 1))
    (hU' : VanishesOutside U' (fun i => i = 0 ∨ i = 1)) (trv : E.X 2 →ₗ[S] S)
    (hker : ∀ z : E.X 2, E.d 2 3 rfl z = 0 → trv z = 0 → ∃ y, E.d 1 2 rfl y = z)
    (hcup : ∀ (u : U.X 1) (v : U'.X 1), trv (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι'.f 1 1 rfl v)) = 0) :
    LocalTruncIsotropy ι ι' P :=
  ofTruncZero (pair_eq_zero_of_11 (truncBounds_of hU hU') _ fun u v => by
    have hc := cocycle_of_trunc _ (pair11_cocycle (truncBounds_of hU hU')
      (truncPair (pullPair P ι ι')) u v)
    obtain ⟨y, hy⟩ := hker _ hc (hcup u v)
    change (truncSub E 2).mkQ (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι'.f 1 1 rfl v)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, truncSub_of_eq E rfl]
    exact ⟨y, hy⟩)

theorem kummerTruncIsotropy_h (hU : VanishesOutside U (fun i => i = 0 ∨ i = 1))
    (hU' : VanishesOutside U' (fun i => i = 0 ∨ i = 1)) (trv : E.X 2 →ₗ[S] S)
    (hker : ∀ z : E.X 2, E.d 2 3 rfl z = 0 → trv z = 0 → ∃ y, E.d 1 2 rfl y = z)
    (hcup : ∀ (u : U.X 1) (v : U'.X 1), trv (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι'.f 1 1 rfl v)) = 0) :
    (kummerTruncIsotropy hU hU' trv hker hcup).h = fun _ _ _ _ => 0 :=
  rfl

/-- **Uniqueness**: for conditions concentrated in degrees `0, 1`, every `τ≥2` isotropy homotopy
projects to zero in `τ≥2 E` (the ambiguity group vanishes). -/
theorem trunc_h_eq_zero (hU : VanishesOutside U (fun i => i = 0 ∨ i = 1))
    (hU' : VanishesOutside U' (fun i => i = 0 ∨ i = 1)) (J : LocalTruncIsotropy ι ι' P)
    (i j k : ℤ) (h : i + j = k + 1) (u : U.X i) (v : U'.X j) :
    (truncSub E k).mkQ (J.h i j k h u v) = 0 :=
  nullHomotopy_eq_zero (truncBounds_of hU hU') (fun i j k h => (J.h i j k h).compr₂ (truncSub E k).mkQ)
    i j k h u v

end Interface

section Two

variable {U U' L L' E : GCx ℤ_[2]} {ι : GHom U L} {ι' : GHom U' L'} {P : GPair L L' E}

/-- The trace descended to `τ≥2 E` in degree two. -/
def truncTrace (trv : E.X 2 →ₗ[ℤ_[2]] ℤ_[2]) (htrv : ∀ y, trv (E.d 1 2 rfl y) = 0) :
    (truncGe2 E).X 2 →ₗ[ℤ_[2]] ℤ_[2] :=
  (truncSub E 2).liftQ trv (by
    rw [truncSub_of_eq E rfl]
    rintro _ ⟨y, rfl⟩
    exact htrv y)

/-- **Kummer-condition isotropy into `τ≥2` over `ℤ₂`** (tex L3443–3450: "finite isotropy makes every
value divisible by every power of two, hence zero"; PROVED via `derivedKummerStep_trunc`): for
conditions concentrated in degrees `0, 1`, a local trace killing coboundaries whose kernel on
degree-two cocycles consists of coboundaries, and `(1, 1)` cup values whose traces are divisible by
every power of two, the zero family is a `τ≥2` isotropy homotopy. -/
def kummerTruncIsotropy_two (hU : VanishesOutside U (fun i => i = 0 ∨ i = 1))
    (hU' : VanishesOutside U' (fun i => i = 0 ∨ i = 1)) (trv : E.X 2 →ₗ[ℤ_[2]] ℤ_[2])
    (htrv : ∀ y, trv (E.d 1 2 rfl y) = 0)
    (hker : ∀ z : E.X 2, E.d 2 3 rfl z = 0 → trv z = 0 → ∃ y, E.d 1 2 rfl y = z)
    (hdiv : ∀ (a : ℕ) (u : U.X 1) (v : U'.X 1),
      (2 : ℤ_[2]) ^ a ∣ trv (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι'.f 1 1 rfl v))) :
    LocalTruncIsotropy ι ι' P :=
  ofTruncZero (derivedKummerStep_trunc (truncBounds_of hU hU') (truncPair (pullPair P ι ι'))
    (truncTrace trv htrv) (fun t ht he => by
      obtain ⟨z, rfl⟩ := (truncSub E 2).mkQ_surjective t
      obtain ⟨y, hy⟩ := hker z (cocycle_of_trunc z ht) he
      change (truncSub E 2).mkQ z = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, truncSub_of_eq E rfl]
      exact ⟨y, hy⟩) hdiv).1

theorem kummerTruncIsotropy_two_h (hU : VanishesOutside U (fun i => i = 0 ∨ i = 1))
    (hU' : VanishesOutside U' (fun i => i = 0 ∨ i = 1)) (trv : E.X 2 →ₗ[ℤ_[2]] ℤ_[2])
    (htrv : ∀ y, trv (E.d 1 2 rfl y) = 0)
    (hker : ∀ z : E.X 2, E.d 2 3 rfl z = 0 → trv z = 0 → ∃ y, E.d 1 2 rfl y = z)
    (hdiv : ∀ (a : ℕ) (u : U.X 1) (v : U'.X 1),
      (2 : ℤ_[2]) ^ a ∣ trv (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι'.f 1 1 rfl v))) :
    (kummerTruncIsotropy_two hU hU' trv htrv hker hdiv).h = fun _ _ _ _ => 0 :=
  rfl

end Two

end ZInQ.Contrib.CloudB3RC53.Duality
