import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.GaloisModel
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Chebotarev
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.TraceModelInstance
import ZInQKernel.Contrib.OneProof.RC.TateWiring.Image

/-!
# Theorem 5.3, Lane RC24: the constituent model over `G_ℚ`, on reduced expansions

Manuscript `diophantine_zq.tex`, App F, proof of Proposition `ex:app-coefficient-rules`
(tex 9447–9976): the integral trace module (tex 9638–9668) and the constituent operators
(tex 9705–9797).

**Reduced expansions (round 3).** The text reads every identity of the trace argument as an
identity of coefficientwise reduced expansions: "In the following trace argument a reduced
expansion means coefficientwise reduction modulo `𝔪_coef` … No saturation of the integral Fourier
module is assumed, and no identification of its abstract quotient with all reduced expansions is
needed" (tex 9639–9646); "the conclusion is an identity of coefficientwise reduced expansions"
(9716–9717); the trace identities hold "on the reduced trace orbit of `F_U`" (9728–9729). The
model therefore carries the integral Fourier expansion `expand : Λ → (C → 𝒪)` of the integral
module and works on the module of reduced expansions `Mexp`, the image of `Λ` under
coefficientwise reduction modulo `𝔪` (`redE`). The operators act there because they preserve
coefficientwise congruences (`cong_t`, `cong_d`, GLUE: good Hecke operations satisfy
`(T_q f)[n] = f[qn] + q(⟨q⟩f)[n/q]`, and the scalar trace and determinant operators are their
Chebotarev limits, tex 9658–9668). `det_orbit`, `two_fresh`, the defining condition of `N_U`
(`consN`) and the readings `read` are stated on reduced expansions. Round 2 stated them as
membership in the abstract submodule `𝔪Λ`; without saturation, coefficientwise vanishing modulo
`𝔪` does not give that, so the old form was stronger than the text. Membership in `𝔪Λ` is now
the separate hypothesis `GaloisConstituentModel.Saturated`, which the text does not assume. Only
the bridge to lane RC0's `ConstituentModelRel`, whose reduced module is `Λ/𝔪Λ`, uses it
(`RelBridge.lean`).

* `GaloisConstituentModel T R ap B chiType`: constituents `ρ` over `G_ℚ`, the integral module `Λ`,
  its Fourier expansion, genuine Frobenius elements, `chiBit := bitChar`, and `N_U := consN …`
  defined from the characters and the reduced trace orbit. The fields `level_red`, `N_anti`,
  `N_chi`, `typ_frob`, `bit_frob` and `chi_surj` (good `U`) of lane RC0 are PROVED here.
* `GaloisConstituentModel.toGaloisTraceModel`: the module of reduced expansions `Mexp` with the
  induced operators is a `GaloisTraceModel`. `consN` is `galN` of the induced operators
  (`consN_eq_galN`). `toGaloisDensityModel` gives the density form, given openness and
  unramifiedness. The readings and RC2's rules follow.
* Non-vacuity with a genuine Galois representation: for an elliptic curve `E/ℚ`,
  `tateConstituentModel'` has one constituent, the `2`-adic Tate representation of `E`. Its data
  are the `ℤ₂`-lattice of integral vectors, its coordinate as the Fourier expansion, and the zero
  forms. Its module of reduced expansions is nonzero (`tateConstituentModelOf_nontrivial`).
  **The constituents of the actual forms `F_U = θ H_U` are weight-two cuspidal newforms and
  Eisenstein character pairs (tex 9647–9654, 9762–9771), not `E` or its twists; the Tate
  representation of `E` only shows that the structure is inhabited by a genuine Galois
  representation.**

DEPARTURE (the constituent representations as data). Mathlib has no Galois representations
attached to modular forms. The field `ρ` therefore carries the representations as data. Their
existence is Carayol's theorem (PRINT, tex 9773–9797). The properties of them that the proof uses
enter through these fields, all stated for the operators built from `ρ`:
`stable_t`, `stable_d`, `cong_t` and `cong_d` (GLUE); `det_orbit`, `two_fresh` and the inputs
`reading`, `o12` (ELLIOT).

Kinds: `PROVED` (a Lean proof), `PRINT` (a printed theorem taken as a field), `GLUE` (a
textbook fact taken as a field), `ELLIOT` (a step of the manuscript's argument taken as a field
or input), `definition`.

References: [Carayol] H. Carayol, *Sur les représentations `ℓ`-adiques associées aux formes
modulaires de Hilbert*, Ann. Sci. École Norm. Sup. (4) 19 (1986), 409–468, §§0.3–0.7,
Théorème A, pp. 409–411 (the locator of tex 9778; statement page `UNVERIFIED` here).
[Neukirch] J. Neukirch, *Algebraic number theory*, Grundlehren 322 (Springer 1999), Ch. VII,
Theorem (13.4) (Čebotarev's density theorem; statement page `UNVERIFIED`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Odd ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Finset

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-! ## The lattice operators and coefficientwise reduction -/

section Lattice

variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]

/-- `t(g)` on an integral module `Λ` preserved by the scalar traces of `ρ` (tex 9762–9771).
Kind: definition. -/
def latT (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) (g : GalQ) : Λ →ₗ[O] Λ :=
  ((tV ρ g).restrictScalars O).restrict (hst g)

/-- `d(g)` on an integral module `Λ` preserved by the determinants of `ρ` (tex 9762–9771).
Kind: definition. -/
def latD (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (hsd : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ) (g : GalQ) : Λ →ₗ[O] Λ :=
  ((dV ρ g).restrictScalars O).restrict (hsd g)

/-- Kind: PROVED (definition). -/
theorem latT_coe (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) (g : GalQ) (v : Λ) :
    (latT ρ Λ hst g v : I → K) = tV ρ g v := rfl

/-- Kind: PROVED (definition). -/
theorem latD_coe (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (hsd : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ) (g : GalQ) (v : Λ) :
    (latD ρ Λ hsd g v : I → K) = dV ρ g v := rfl

/-- **Coefficientwise reduction modulo `𝔪`** of the integral expansion (tex 9639–9641: "a reduced
expansion means coefficientwise reduction modulo `𝔪_coef`"). Kind: definition. -/
def redExpOf (m : Ideal O) {Λ : Submodule O (I → K)} {C : Type} (expand : Λ →ₗ[O] (C → O)) :
    Λ →ₗ[O] (C → O ⧸ m) :=
  (LinearMap.compLeft (Submodule.mkQ m) C) ∘ₗ expand

/-- Kind: PROVED (definition). -/
theorem redExpOf_apply (m : Ideal O) {Λ : Submodule O (I → K)} {C : Type}
    (expand : Λ →ₗ[O] (C → O)) (v : Λ) (n : C) :
    redExpOf m expand v n = Ideal.Quotient.mk m (expand v n) := rfl

/-- **`𝔪Λ` reduces to zero coefficientwise** (the reduced expansions are annihilated by `𝔪`; the
converse, saturation, is not assumed by the text, tex 9644–9646). Kind: PROVED. -/
theorem le_ker_redExpOf (m : Ideal O) {Λ : Submodule O (I → K)} {C : Type}
    (expand : Λ →ₗ[O] (C → O)) :
    (m • ⊤ : Submodule O Λ) ≤ LinearMap.ker (redExpOf m expand) := by
  intro v hv
  refine Submodule.smul_induction_on hv (fun r hr w _ => ?_) (fun x y hx hy => ?_)
  · rw [LinearMap.mem_ker, map_smul]
    funext n
    show r • redExpOf m expand w n = 0
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hr,
      zero_mul]
  · exact Submodule.add_mem _ hx hy

/-- **The reduced trace orbit**: `(g, U) ↦` the reduced expansion of `t(g) F_U` (tex 9716–9729).
Kind: definition. -/
def redTrace (m : Ideal O) {Λ : Submodule O (I → K)} {C : Type} (expand : Λ →ₗ[O] (C → O))
    (ρ : I → GalQ →* GL (Fin 2) K) (hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) (F : Finset ℕ → Λ) :
    GalQ → Finset ℕ → (C → O ⧸ m) :=
  fun g U => redExpOf m expand (latT ρ Λ hst g (F U))

end Lattice

/-! ## The subgroup `N_U` of a reduced trace orbit -/

section ConsN

variable {Y : Type*}

/-- **The subgroup `N_U` cut out by the characters and the reduced trace orbit** (tex 9663–9668,
9745–9750, 9919–9921). It consists of the `n ∈ G_ℚ` such that
* `χ_type(n) = 1` and `χ_s(n) = 1` for `s ∈ U`;
* `rt(gn, U') = rt(g, U')` for every `g ∈ G_ℚ` and every `U' ⊆ U`.

For the constituent model, `rt(g, U')` is the reduced expansion of `t(g)F_{U'}` (`redTrace`),
and `N_U` is `galN` of the induced operators (`GaloisConstituentModel.consN_eq_galN`). Kind:
definition. -/
def consN (chiType : GalQ →* Multiplicative L) (rt : GalQ → Finset ℕ → Y) (U : Finset ℕ) :
    Subgroup GalQ where
  carrier := {n | chiType n = 1 ∧ (∀ s ∈ U, bitChar s n = 1) ∧
    ∀ g : GalQ, ∀ U' ⊆ U, rt (g * n) U' = rt g U'}
  one_mem' := ⟨map_one _, fun _ _ => map_one _, fun g _ _ => by rw [mul_one]⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨by rw [map_mul, ha.1, hb.1, mul_one], fun s hs => by
      rw [map_mul, ha.2.1 s hs, hb.2.1 s hs, mul_one], fun g U' hU' => ?_⟩
    rw [← mul_assoc, hb.2.2 (g * a) U' hU', ha.2.2 g U' hU']
  inv_mem' := by
    intro a ha
    refine ⟨by rw [map_inv, ha.1, inv_one], fun s hs => by rw [map_inv, ha.2.1 s hs, inv_one],
      fun g U' hU' => ?_⟩
    have h := ha.2.2 (g * a⁻¹) U' hU'
    rw [inv_mul_cancel_right] at h
    exact h.symm

variable {chiType : GalQ →* Multiplicative L} {rt : GalQ → Finset ℕ → Y}

/-- Membership in `consN`. Kind: PROVED (definition). -/
theorem mem_consN {U : Finset ℕ} {n : GalQ} :
    n ∈ consN chiType rt U ↔ chiType n = 1 ∧ (∀ s ∈ U, bitChar s n = 1) ∧
      ∀ g : GalQ, ∀ U' ⊆ U, rt (g * n) U' = rt g U' :=
  Iff.rfl

/-- **For an orbit constant in `g` (e.g. the zero forms), `N_U` is the common kernel of the type
character and the `χ_s`, `s ∈ U`.** Kind: PROVED. -/
theorem mem_consN_of_const (hrt : ∀ g U, rt g U = rt 1 U) {U : Finset ℕ} {n : GalQ} :
    n ∈ consN chiType rt U ↔ chiType n = 1 ∧ ∀ s ∈ U, bitChar s n = 1 :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun g U' _ => by rw [hrt, hrt g]⟩⟩

/-- **For an orbit constant in `g`, `N_U` has finite index** when the type alphabet is finite.
Kind: PROVED (it contains the kernel of the joint character, valued in a finite group). -/
theorem consN_const_finiteIndex [Finite L] (hrt : ∀ g U, rt g U = rt 1 U) (U : Finset ℕ) :
    (consN chiType rt U).FiniteIndex := by
  let φ : GalQ →* Multiplicative L × (U → Multiplicative (ZMod 2)) :=
    chiType.prod (MonoidHom.pi fun s : U => bitChar s)
  have hle : φ.ker ≤ consN chiType rt U := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn
    refine (mem_consN_of_const hrt).mpr ⟨congrArg Prod.fst hn, fun s hs => ?_⟩
    exact congrFun (congrArg Prod.snd hn) ⟨s, hs⟩
  have : φ.ker.FiniteIndex := Subgroup.finiteIndex_ker φ
  exact Subgroup.finiteIndex_of_le hle

/-- **Chebotarev relative to `N_U` for an orbit constant in `g`, by Dirichlet** (tex 2151–2174,
9938–9942). Kind: PROVED (`exists_good_frob`). -/
theorem consN_const_chebotarev (T : TypeData L ε) (htyp : IsTypeChar T chiType)
    (hrt : ∀ g U, rt g U = rt 1 U) {frob : ℕ → GalQ}
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q) (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s)
    (g : GalQ) (avoid : Finset ℕ) :
    ∃ q h, ∃ n ∈ consN chiType rt U, T.Good q ∧ q ∉ avoid ∧ frob q = h * g * h⁻¹ * n := by
  obtain ⟨q, hq, -, hqa, h1, h2⟩ := exists_good_frob T htyp hfrob U avoid hU
    (Multiplicative.toAdd (chiType g)) (fun s => Multiplicative.toAdd (bitChar s g))
  refine ⟨q, 1, g⁻¹ * frob q, (mem_consN_of_const hrt).mpr ⟨?_, fun s hs => ?_⟩, hq, hqa,
    by group⟩
  · rw [map_mul, map_inv, h1, ofAdd_toAdd, inv_mul_cancel]
  · rw [map_mul, map_inv, h2 s hs, ofAdd_toAdd, inv_mul_cancel]

end ConsN

/-! ## The constituent model over `G_ℚ` -/

/-- **The constituent model of the integral trace module over `G_ℚ`, on reduced expansions**,
within the budget `B`, for the type character `chiType` (tex 9638–9668, 9705–9797). It is lane
RC0's `ConstituentModelRel` with `G := G_ℚ`, genuine Frobenius elements (`frob_spec`),
`chiBit := bitChar`, and `N_U := consN chiType (redTrace …) U` defined. Every identity of the
trace argument is an identity of coefficientwise reduced expansions (tex 9639–9646, 9716–9717,
9728–9729; see the module docstring). This constituent interface is not the wired density leaf:
the leaf asks for density models (`Chebotarev.lean`), which `toGaloisDensityModel` builds from it
given its inputs, openness and unramifiedness.

Kinds:
* `ρ`: PRINT ([Carayol, §§0.3–0.7, Théorème A, pp. 409–411], tex 9773–9797, stated as data);
* `stable_t`, `stable_d`, `cong_t`, `cong_d`, `kummer`, `finiteIndex`: GLUE;
* `det_orbit`, `two_fresh`: ELLIOT;
* `chebotarev`: PRINT ([Neukirch, Ch. VII, Theorem (13.4)]; tex 9666–9668, 9919–9921);
* `I`, `K`, `O`, `m`, `Λ`, `C`, `coefK`, `expand`, `expand_spec`, `F`, `read`, `frob_spec`:
  definition (data of the construction, tex 9638–9668).

The ELLIOT inputs `reading`, `o12` are `GaloisConstituentModel.Inputs`. Budget (tex 9447–9468,
9649–9654, 9741–9745, 10533–10548): the fields about one `U` are stated for `U` a set of good
primes with `|U| + 1 ≤ B`. Owner: RC12 (App F), Lane RC24. -/
structure GaloisConstituentModel (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ)
    (chiType : GalQ →* Multiplicative L) where
  /-- the constituents, with their multiplicities and degeneracies (tex 9649–9654, 9762–9771) -/
  I : Type
  /-- the characteristic-zero coefficient field, containing all constituents (tex 9649–9652) -/
  K : Type
  [instK : Field K]
  /-- the coefficient valuation ring `𝒪_coef` (tex 9638–9641) -/
  O : Type
  [instO : CommRing O]
  [instAlg : Algebra O K]
  /-- the maximal ideal `𝔪_coef` (tex 9638–9641) -/
  m : Ideal O
  /-- `2 ∈ 𝔪_coef`: the coefficient place lies above two (tex 9780–9781) -/
  two_mem : (2 : O) ∈ m
  /-- PRINT ([Carayol, Théorème A], tex 9773–9797; stated as data): the two-dimensional Galois
  representations of the constituents (the sum of the two characters on an Eisenstein
  constituent, tex 9652–9654, 9762–9771) -/
  ρ : I → GalQ →* GL (Fin 2) K
  /-- the integral module generated by the translates of the forms (tex 9655–9665) -/
  Λ : Submodule O (I → K)
  /-- GLUE (tex 9663–9668): `Λ` is preserved by the scalar trace operators -/
  stable_t : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ
  /-- GLUE (tex 9663–9668): `Λ` is preserved by the determinant operators -/
  stable_d : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ
  /-- the Fourier indices of the coordinates (tex 9661–9662) -/
  C : Type
  /-- the Fourier expansion of the characteristic-zero space (tex 9655–9662) -/
  coefK : (I → K) →ₗ[K] (C → K)
  /-- the integral Fourier coefficients of the integral module (tex 9655–9662) -/
  expand : Λ →ₗ[O] (C → O)
  /-- definition: `expand` records the Fourier coefficients of the integral forms in `𝒪`
  (the translates remain integral, tex 9655–9660) -/
  expand_spec : ∀ (v : Λ) (n : C), algebraMap O K (expand v n) = coefK v n
  /-- GLUE (tex 9658–9668: good Hecke operations `(T_q f)[n] = f[qn] + q(⟨q⟩f)[n/q]`, of which
  the scalar trace operators are Chebotarev limits): `t(g)` preserves coefficientwise
  congruences modulo `𝔪` -/
  cong_t : ∀ g (v : Λ), redExpOf m expand v = 0 → redExpOf m expand (latT ρ Λ stable_t g v) = 0
  /-- GLUE (tex 9658–9668, diamond operations): `d(g)` preserves coefficientwise congruences -/
  cong_d : ∀ g (v : Λ), redExpOf m expand v = 0 → redExpOf m expand (latD ρ Λ stable_d g v) = 0
  /-- the integral forms `F_U = θ H_U` (tex 9647–9648, 9672) for `U` a set of good primes within
  the budget; the values elsewhere are constrained by no field -/
  F : Finset ℕ → Λ
  /-- the coefficient-one functionals on reduced expansions (tex 9686–9690) -/
  read : Finset ℕ → (C → O ⧸ m) →+ ZMod 2
  /-- the Frobenius elements in `G_ℚ` -/
  frob : ℕ → GalQ
  /-- definition: `frob q` is a genuine arithmetic Frobenius element at every good prime `q` -/
  frob_spec : ∀ q, T.Good q → IsFrobAt (frob q) q
  /-- ELLIOT (tex 9712–9733: the diamond/trace-orbit calculation; "the conclusion is an identity of
  coefficientwise reduced expansions", 9716–9717), within the budget: `d(u) t(v) F_U` and
  `t(v) F_U` have the same reduced expansion -/
  det_orbit : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ u v,
    redExpOf m expand (latD ρ Λ stable_d u (latT ρ Λ stable_t v (F U))) =
      redExpOf m expand (latT ρ Λ stable_t v (F U))
  /-- ELLIOT (tex 9741–9745: "It follows that `t(g)t(h)F_U = 0` after reduction"), within the
  budget: the reduced expansion of `t(g) t(h) F_U` vanishes -/
  two_fresh : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g h,
    redExpOf m expand (latT ρ Λ stable_t g (latT ρ Λ stable_t h (F U))) = 0
  /-- GLUE (Kummer theory for the several radicals, tex 9745–9750), within the budget -/
  kummer : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g, chiType g = 1 →
    (∀ s ∈ U, bitChar s g = 1) →
      g ∈ Subgroup.closure (sqSet GalQ) ⊔ consN chiType (redTrace m expand ρ stable_t F) U
  /-- GLUE (continuity on the finite module, tex 9663–9668), within the budget: `G_ℚ/N_U` is
  finite -/
  finiteIndex : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
    (consN chiType (redTrace m expand ρ stable_t F) U).FiniteIndex
  /-- PRINT ([Neukirch, Ch. VII, Theorem (13.4)], in the finite quotient `G_ℚ/N_U`, tex 9666–9668,
  9919–9921), within the budget -/
  chebotarev : ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
    ∀ (g : GalQ) (avoid : Finset ℕ), ∃ q h, ∃ n ∈ consN chiType (redTrace m expand ρ stable_t F) U,
      T.Good q ∧ q ∉ avoid ∧ frob q = h * g * h⁻¹ * n

namespace GaloisConstituentModel

variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
  {chiType : GalQ →* Multiplicative L} (X : GaloisConstituentModel T R ap B chiType)

attribute [instance] GaloisConstituentModel.instK GaloisConstituentModel.instO
  GaloisConstituentModel.instAlg

/-- `t(g)` on `Λ`. Kind: definition. -/
abbrev tΛ (g : GalQ) : X.Λ →ₗ[X.O] X.Λ := latT X.ρ X.Λ X.stable_t g

/-- `d(g)` on `Λ`. Kind: definition. -/
abbrev dΛ (g : GalQ) : X.Λ →ₗ[X.O] X.Λ := latD X.ρ X.Λ X.stable_d g

/-- Coefficientwise reduction of the integral expansion (tex 9639–9641). Kind: definition. -/
abbrev redE : X.Λ →ₗ[X.O] (X.C → X.O ⧸ X.m) := redExpOf X.m X.expand

/-- The subgroup `N_U` of the model. Kind: definition. -/
abbrev N (U : Finset ℕ) : Subgroup GalQ :=
  consN chiType (redTrace X.m X.expand X.ρ X.stable_t X.F) U

/-! ### RC0's fields, PROVED -/

/-- **`level_red`** (RC0's field, on reduced expansions; tex 9524–9548, 9663–9668): for
`n ∈ N_U` the reduced expansions of `t(gn) F_U` and `t(g) F_U` agree. Kind: PROVED (definition of
`consN`). -/
theorem level_red (U : Finset ℕ) (g n : GalQ) (hn : n ∈ X.N U) :
    X.redE (X.tΛ (g * n) (X.F U)) = X.redE (X.tΛ g (X.F U)) :=
  hn.2.2 g U (subset_refl U)

/-- **`N_anti`** (RC0's field). Kind: PROVED (definition of `consN`). -/
theorem N_anti (U U' : Finset ℕ) (h : U' ⊆ U) : X.N U ≤ X.N U' :=
  fun _ hn => ⟨hn.1, fun s hs => hn.2.1 s (h hs), fun g U'' hU'' => hn.2.2 g U'' (hU''.trans h)⟩

/-- **`N_chi`** (RC0's field). Kind: PROVED (definition of `consN`). -/
theorem N_chi (U : Finset ℕ) : ∀ n ∈ X.N U, chiType n = 1 ∧ ∀ s ∈ U, bitChar s n = 1 :=
  fun _ hn => ⟨hn.1, hn.2.1⟩

/-- **`typ_frob`** (RC0's field; tex 2017–2020, 9936–9940). Kind: PROVED. -/
theorem typ_frob (htyp : IsTypeChar T chiType) (q : ℕ) (hq : T.Good q) :
    chiType (X.frob q) = Multiplicative.ofAdd (T.typ q) :=
  htyp q _ hq (X.frob_spec q hq)

/-- **`bit_frob`** (RC0's field; tex 9938–9942). Kind: PROVED (`bitChar_of_good`). -/
theorem bit_frob (q s : ℕ) (hq : T.Good q) (hs : T.Good s) (hqs : q ≠ s) :
    bitChar s (X.frob q) = Multiplicative.ofAdd (legBit q s) :=
  bitChar_of_good T hq hs hqs (X.frob_spec q hq)

include X in
/-- **`chi_surj` at sets of good primes** (RC0's field restricted to good `U`; at other `U` it
is false, `not_chi_surj_all`). Kind: PROVED (`exists_good_frob`). -/
theorem chi_surj (htyp : IsTypeChar T chiType) (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (ℓ : L)
    (b : ℕ → ZMod 2) :
    ∃ g : GalQ, chiType g = Multiplicative.ofAdd ℓ ∧
      ∀ s ∈ U, bitChar s g = Multiplicative.ofAdd (b s) := by
  obtain ⟨q, -, -, -, h1, h2⟩ := exists_good_frob T htyp X.frob_spec U ∅ hU ℓ b
  exact ⟨_, h1, h2⟩

/-! ### The module of reduced expansions -/

/-- **The module of coefficientwise reduced expansions**: the image of `Λ` under reduction
modulo `𝔪` (tex 9639–9646). Kind: definition. -/
abbrev Mexp : Submodule X.O (X.C → X.O ⧸ X.m) := LinearMap.range X.redE

/-- The reduced expansion of a vector of `Λ`, in `Mexp`. Kind: definition. -/
def redM : X.Λ →ₗ[X.O] X.Mexp := X.redE.rangeRestrict

/-- Kind: PROVED (definition). -/
theorem redM_coe (v : X.Λ) : (X.redM v : X.C → X.O ⧸ X.m) = X.redE v := rfl

/-- Every reduced expansion comes from `Λ`. Kind: PROVED. -/
theorem redM_surjective : Function.Surjective X.redM := LinearMap.surjective_rangeRestrict _

/-- Kind: PROVED. -/
theorem redM_eq_iff (v w : X.Λ) : X.redM v = X.redM w ↔ X.redE v = X.redE w :=
  Subtype.ext_iff

/-- Kind: PROVED. -/
theorem redM_eq_zero_iff (v : X.Λ) : X.redM v = 0 ↔ X.redE v = 0 := by
  rw [← map_zero X.redM, redM_eq_iff, map_zero]

/-- `2 = 0` on reduced expansions (`2 ∈ 𝔪`). Kind: PROVED. -/
theorem two_nsmul_exp (y : X.C → X.O ⧸ X.m) : 2 • y = 0 := by
  funext n
  have h2 : ((2 : ℕ) : X.O ⧸ X.m) = 0 := by
    rw [show ((2 : ℕ) : X.O ⧸ X.m) = Ideal.Quotient.mk X.m (2 : X.O) by
      rw [map_ofNat]; rfl]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr X.two_mem
  show 2 • y n = 0
  rw [nsmul_eq_mul, h2, zero_mul]

/-- `2 = 0` on the module of reduced expansions. Kind: PROVED. -/
theorem two_nsmul_Mexp (x : X.Mexp) : 2 • x = 0 :=
  Subtype.ext (X.two_nsmul_exp (x : X.C → X.O ⧸ X.m))

/-- The `𝔽₂`-structure of the module of reduced expansions. Kind: definition. -/
abbrev modMexp : Module (ZMod 2) X.Mexp := AddCommGroup.zmodModule X.two_nsmul_Mexp

/-- **An `𝒪`-linear endomorphism of `Λ` preserving coefficientwise congruences acts on the
reduced expansions** (through `Λ / ker(reduction) ≅ Mexp`). Kind: definition. -/
def opE (f : X.Λ →ₗ[X.O] X.Λ) (hf : ∀ v, X.redE v = 0 → X.redE (f v) = 0) :
    X.Mexp →ₗ[X.O] X.Mexp :=
  (X.redE.quotKerEquivRange.toLinearMap ∘ₗ
    (LinearMap.ker X.redE).mapQ (LinearMap.ker X.redE) f
      (fun v hv => LinearMap.mem_ker.mpr (hf v (LinearMap.mem_ker.mp hv)))) ∘ₗ
      X.redE.quotKerEquivRange.symm.toLinearMap

/-- Kind: PROVED. -/
theorem opE_redM (f : X.Λ →ₗ[X.O] X.Λ) (hf : ∀ v, X.redE v = 0 → X.redE (f v) = 0)
    (v : X.Λ) : X.opE f hf (X.redM v) = X.redM (f v) := by
  apply Subtype.ext
  simp only [opE, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [show X.redM v = ⟨X.redE v, LinearMap.mem_range_self _ v⟩ from rfl,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply]
  rfl

attribute [local instance] GaloisConstituentModel.modMexp

/-- `t(g)` on reduced expansions. Kind: definition. -/
def tE (g : GalQ) : X.Mexp →ₗ[ZMod 2] X.Mexp :=
  (X.opE (X.tΛ g) (fun v hv => X.cong_t g v hv)).toAddMonoidHom.toZModLinearMap 2

/-- `d(g)` on reduced expansions. Kind: definition. -/
def dE (g : GalQ) : X.Mexp →ₗ[ZMod 2] X.Mexp :=
  (X.opE (X.dΛ g) (fun v hv => X.cong_d g v hv)).toAddMonoidHom.toZModLinearMap 2

/-- The reduced forms `F_U`. Kind: definition. -/
def FE (U : Finset ℕ) : X.Mexp := X.redM (X.F U)

/-- The coefficient-one functionals on the module of reduced expansions. Kind: definition. -/
def readE (U : Finset ℕ) : X.Mexp →ₗ[ZMod 2] ZMod 2 :=
  ((X.read U).comp X.Mexp.subtype.toAddMonoidHom).toZModLinearMap 2

/-- Kind: PROVED. -/
theorem tE_redM (g : GalQ) (v : X.Λ) : X.tE g (X.redM v) = X.redM (X.tΛ g v) :=
  X.opE_redM _ (fun v hv => X.cong_t g v hv) v

/-- Kind: PROVED. -/
theorem dE_redM (g : GalQ) (v : X.Λ) : X.dE g (X.redM v) = X.redM (X.dΛ g v) :=
  X.opE_redM _ (fun v hv => X.cong_d g v hv) v

/-- Kind: PROVED (definition). -/
theorem readE_redM (U : Finset ℕ) (v : X.Λ) : X.readE U (X.redM v) = X.read U (X.redE v) := rfl

/-- **`trace_mul` on reduced expansions** (tex 9734–9737). Kind: PROVED (the matrix identity on
each constituent, batch 3's `tV_mul`, then reduction). -/
theorem trace_mul (g h : GalQ) (x : X.Mexp) :
    X.tE g (X.tE h x) = X.tE (g * h) x + X.dE h (X.tE (g * h⁻¹) x) := by
  obtain ⟨v, rfl⟩ := X.redM_surjective x
  rw [tE_redM, tE_redM, tE_redM, tE_redM, dE_redM, ← map_add]
  congr 1
  apply Subtype.ext
  exact tV_mul X.ρ g h (v : X.I → X.K)

/-- **`det_orbit` on reduced expansions** (tex 9712–9733), within the budget. Kind: PROVED (from
the ELLIOT field `det_orbit`). -/
theorem det_orbit' (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B) (u v : GalQ) :
    X.dE u (X.tE v (X.FE U)) = X.tE v (X.FE U) := by
  rw [FE, tE_redM, dE_redM, redM_eq_iff]
  exact X.det_orbit U hU hUB u v

/-- **`two_fresh` on reduced expansions** (tex 9741–9745), within the budget. Kind: PROVED (from
the ELLIOT field `two_fresh`). -/
theorem two_fresh' (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B) (g h : GalQ) :
    X.tE g (X.tE h (X.FE U)) = 0 := by
  rw [FE, tE_redM, tE_redM, redM_eq_zero_iff]
  exact X.two_fresh U hU hUB g h

/-- **`trace_one`** (tex 9739). Kind: PROVED (`tr 1 = 2`, `2 ∈ 𝔪`). -/
theorem trace_one (x : X.Mexp) : X.tE 1 x = (2 : ZMod 2) • x := by
  rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  obtain ⟨v, rfl⟩ := X.redM_surjective x
  rw [tE_redM]
  have e : X.tΛ 1 v = (2 : ℕ) • v := by
    apply Subtype.ext
    show tV X.ρ 1 (v : X.I → X.K) = (((2 : ℕ) • v : X.Λ) : X.I → X.K)
    rw [tV_one, two_smul]
    simp [two_nsmul]
  rw [e, map_nsmul]
  exact X.two_nsmul_Mexp _

/-- **`t` is a class function** (tex 9762–9771). Kind: PROVED (batch 3's `tV_conj`). -/
theorem t_class (g h : GalQ) : X.tE (h * g * h⁻¹) = X.tE g := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := X.redM_surjective x
  rw [tE_redM, tE_redM]
  congr 1
  apply Subtype.ext
  show tV X.ρ (h * g * h⁻¹) (v : X.I → X.K) = tV X.ρ g v
  rw [tV_conj]

/-- **The induced traces agree on `F_U` iff the reduced trace orbit does.** Kind: PROVED. -/
theorem tE_FE_eq_iff (g n : GalQ) (U : Finset ℕ) :
    X.tE (g * n) (X.FE U) = X.tE g (X.FE U) ↔
      redTrace X.m X.expand X.ρ X.stable_t X.F (g * n) U =
        redTrace X.m X.expand X.ρ X.stable_t X.F g U := by
  rw [FE, tE_redM, tE_redM, redM_eq_iff]
  rfl

/-- **`level`** (RC0's `TraceModelRel.level`) on reduced expansions. Kind: PROVED. -/
theorem level (U : Finset ℕ) (g n : GalQ) (hn : n ∈ X.N U) :
    X.tE (g * n) (X.FE U) = X.tE g (X.FE U) :=
  (X.tE_FE_eq_iff g n U).mpr (hn.2.2 g U (subset_refl U))

/-- **`N_U` is the subgroup `galN` of the induced operators** (`GaloisModel.lean`). Kind:
PROVED. -/
theorem consN_eq_galN (U : Finset ℕ) : X.N U = galN chiType X.tE X.FE U := by
  ext n
  rw [mem_galN, N, mem_consN]
  exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun g =>
    forall₂_congr fun U' _ => (X.tE_FE_eq_iff g n U').symm))

/-- **`N_U` is normal** (tex 9919–9921). Kind: PROVED (`consN_eq_galN`, `galN_normal`). -/
theorem N_normal (U : Finset ℕ) : (X.N U).Normal := by
  rw [X.consN_eq_galN U]
  exact galN_normal X.t_class

/-! ### The genuine Galois trace model of the constituent model -/

/-- **The two ELLIOT inputs**, for the induced operators on reduced expansions: the
coefficient-one reading of a fresh vertex (tex 9671–9704) and (O.12) at coefficient one (tex
9905–9918). Kind: definition. -/
def Inputs : Prop :=
  (∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
      (insert q U).card ≤ B → R (insert q U) = X.readE U (X.tE (X.frob q) (X.FE U))) ∧
  (∀ (U : Finset ℕ) (p : ℕ), p ∈ U → (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g : GalQ,
      ∃ (τ φ : GalQ) (κ0 : ℤ), (κ0 = 1 ∨ κ0 = -1) ∧
        chiType τ = 1 ∧ (∀ s ∈ U, s ≠ p → bitChar s τ = 1) ∧
        bitChar p τ = Multiplicative.ofAdd 1 ∧
        chiType φ = Multiplicative.ofAdd (T.typ p) ∧
        (∀ s ∈ U, s ≠ p → bitChar s φ = Multiplicative.ofAdd (legBit p s)) ∧
        ((Cp (ap p) (-κ0) : ℤ) : ZMod 2) *
            X.readE (U.erase p) (X.tE (g * τ * φ) (X.FE (U.erase p))) -
          ((Cp (ap p) κ0 : ℤ) : ZMod 2) * X.readE (U.erase p) (X.tE (g * φ) (X.FE (U.erase p))) =
        X.readE U (X.tE (g * τ) (X.FE U)) - X.readE U (X.tE g (X.FE U)))

/-- **The genuine Galois trace model of the constituent model** (tex 9638–9771): the module of
reduced expansions `Mexp` with the induced operators, forms and functionals. The abstract
module of `GaloisTraceModel` is instantiated by the reduced expansions. Kind: PROVED. -/
def toGaloisTraceModel (hI : X.Inputs) : GaloisTraceModel T R ap B chiType where
  M := X.Mexp
  instMod := X.modMexp
  t := X.tE
  d := X.dE
  F := X.FE
  read := X.readE
  frob := X.frob
  frob_spec := X.frob_spec
  trace_mul := X.trace_mul
  det_orbit := X.det_orbit'
  two_fresh := X.two_fresh'
  trace_one := X.trace_one
  t_class := X.t_class
  kummer U hU hUB g h1 h2 := by
    rw [← X.consN_eq_galN U]
    exact X.kummer U hU hUB g h1 h2
  finiteIndex U hU hUB := by
    rw [← X.consN_eq_galN U]
    exact X.finiteIndex U hU hUB
  chebotarev U hU hUB g avoid := by
    rw [← X.consN_eq_galN U]
    exact X.chebotarev U hU hUB g avoid
  reading := hI.1
  o12 := hI.2

/-- **The density form** (the model of the wired leaf, `Chebotarev.lean`) from a constituent
model: the module of reduced expansions with the induced operators, given the GLUE openness
(a) and unramifiedness (b) of the induced `N_U`. The constituent model's own `finiteIndex` and
`chebotarev` are not used. Kind: PROVED. -/
def toGaloisDensityModel (hI : X.Inputs) (hopen : GalNOpen T chiType X.tE X.FE B)
    (hunr : GalNUnramified T chiType X.tE X.FE B) : GaloisDensityModel T R ap B chiType where
  M := X.Mexp
  instMod := X.modMexp
  t := X.tE
  d := X.dE
  F := X.FE
  read := X.readE
  frob := X.frob
  frob_spec := X.frob_spec
  trace_mul := X.trace_mul
  det_orbit := X.det_orbit'
  two_fresh := X.two_fresh'
  trace_one := X.trace_one
  t_class := X.t_class
  kummer U hU hUB g h1 h2 := by
    rw [← X.consN_eq_galN U]
    exact X.kummer U hU hUB g h1 h2
  isOpen := hopen
  unramified := hunr
  reading := hI.1
  o12 := hI.2

/-- **The fixed-`U` factorization from the constituent model** (tex 9745–9750). Kind: PROVED. -/
theorem fixedU_of_constituents (hI : X.Inputs) (htyp : IsTypeChar T chiType) :
    FixedUFactorization T R B :=
  (X.toGaloisTraceModel hI).fixedU_of_model htyp

/-- **Primary isolation from the constituent model** (tex 9739, 9947–9948). Kind: PROVED. -/
theorem primary_of_constituents (hI : X.Inputs) (htyp : IsTypeChar T chiType) :
    PrimaryReading T R B :=
  (X.toGaloisTraceModel hI).primary_of_model htyp

/-- **The (O.12) reading from the constituent model** (tex 9905–9945). Kind: PROVED. -/
theorem o12_of_constituents (hI : X.Inputs) (htyp : IsTypeChar T chiType) :
    O12Reading T R ap B :=
  (X.toGaloisTraceModel hI).o12_of_model htyp

/-! ### The unbudgeted forms and saturation (bridges to lane RC0's interfaces) -/

/-- **The unbudgeted forms of the budgeted fields**, on reduced expansions: `det_orbit`,
`two_fresh` and `kummer` at every finite set `U`, `chebotarev` at every set `U` of good primes.
This is NOT given by the text off the budget (tex 9447–9468, 9649–9654, 9741–9745, 10533–10548);
it holds for the zero-form models. Kind: definition (bridge hypothesis, no tex line). -/
def Unbudgeted : Prop :=
  (∀ (U : Finset ℕ) (u v : GalQ), X.redE (X.dΛ u (X.tΛ v (X.F U))) = X.redE (X.tΛ v (X.F U))) ∧
    (∀ (U : Finset ℕ) (g h : GalQ), X.redE (X.tΛ g (X.tΛ h (X.F U))) = 0) ∧
    (∀ (U : Finset ℕ) (g : GalQ), chiType g = 1 → (∀ s ∈ U, bitChar s g = 1) →
      g ∈ Subgroup.closure (sqSet GalQ) ⊔ X.N U) ∧
    (∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → ∀ (g : GalQ) (avoid : Finset ℕ),
      ∃ q h, ∃ n ∈ X.N U, T.Good q ∧ q ∉ avoid ∧ X.frob q = h * g * h⁻¹ * n)

variable {X} in
/-- `det_orbit` at every `U`, from `Unbudgeted`. Kind: PROVED (projection). -/
theorem Unbudgeted.det_orbit (hX : X.Unbudgeted) (U : Finset ℕ) (u v : GalQ) :
    X.redE (X.dΛ u (X.tΛ v (X.F U))) = X.redE (X.tΛ v (X.F U)) :=
  hX.1 U u v

variable {X} in
/-- `two_fresh` at every `U`, from `Unbudgeted`. Kind: PROVED (projection). -/
theorem Unbudgeted.two_fresh (hX : X.Unbudgeted) (U : Finset ℕ) (g h : GalQ) :
    X.redE (X.tΛ g (X.tΛ h (X.F U))) = 0 :=
  hX.2.1 U g h

variable {X} in
/-- `kummer` at every `U`, from `Unbudgeted`. Kind: PROVED (projection). -/
theorem Unbudgeted.kummer (hX : X.Unbudgeted) :
    ∀ (U : Finset ℕ) (g : GalQ), chiType g = 1 → (∀ s ∈ U, bitChar s g = 1) →
      g ∈ Subgroup.closure (sqSet GalQ) ⊔ X.N U :=
  hX.2.2.1

variable {X} in
/-- `chebotarev` at every set `U` of good primes, from `Unbudgeted`. Kind: PROVED
(projection). -/
theorem Unbudgeted.chebotarev (hX : X.Unbudgeted) :
    ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → ∀ (g : GalQ) (avoid : Finset ℕ),
      ∃ q h, ∃ n ∈ X.N U, T.Good q ∧ q ∉ avoid ∧ X.frob q = h * g * h⁻¹ * n :=
  hX.2.2.2

/-- **The unbudgeted forms pass to the Galois trace model** (no tex line). Kind: PROVED. -/
theorem unbudgeted_toGaloisTraceModel (hX : X.Unbudgeted) (hI : X.Inputs) :
    (X.toGaloisTraceModel hI).Unbudgeted := by
  refine ⟨fun U u v => ?_, fun U g h => ?_, fun U g h1 h2 => ?_, fun U hU g avoid => ?_⟩
  · show X.dE u (X.tE v (X.FE U)) = X.tE v (X.FE U)
    rw [FE, tE_redM, dE_redM, redM_eq_iff]
    exact hX.1 U u v
  · show X.tE g (X.tE h (X.FE U)) = 0
    rw [FE, tE_redM, tE_redM, redM_eq_zero_iff]
    exact hX.2.1 U g h
  · show g ∈ Subgroup.closure (sqSet GalQ) ⊔ galN chiType X.tE X.FE U
    rw [← X.consN_eq_galN U]
    exact hX.2.2.1 U g h1 h2
  · show ∃ q h, ∃ n ∈ galN chiType X.tE X.FE U, T.Good q ∧ q ∉ avoid ∧
      X.frob q = h * g * h⁻¹ * n
    rw [← X.consN_eq_galN U]
    exact hX.2.2.2 U hU g avoid

/-- **The reduced trace orbit of zero forms is constant** (zero). Kind: PROVED. -/
theorem redTrace_const_of_forms_eq_zero (hF : ∀ U, X.F U = 0) :
    ∀ g U, redTrace X.m X.expand X.ρ X.stable_t X.F g U =
      redTrace X.m X.expand X.ρ X.stable_t X.F 1 U := by
  intro g U
  simp only [redTrace, hF U, map_zero]

/-- **A constituent model with zero forms satisfies the unbudgeted forms** (no tex line). Kind:
PROVED. -/
theorem unbudgeted_of_forms_eq_zero (hF : ∀ U, X.F U = 0) (htyp : IsTypeChar T chiType) :
    X.Unbudgeted := by
  have hrt := X.redTrace_const_of_forms_eq_zero hF
  refine ⟨fun U u v => ?_, fun U g h => ?_, fun U g h1 h2 => ?_, fun U hU g avoid => ?_⟩
  · simp only [hF U, map_zero]
  · simp only [hF U, map_zero]
  · exact Subgroup.mem_sup_right ((mem_consN_of_const hrt).mpr ⟨h1, h2⟩)
  · exact consN_const_chebotarev T htyp hrt X.frob_spec U hU g avoid

/-- **Saturation of the integral module** (NOT assumed by the text: "No saturation of the
integral Fourier module is assumed, and no identification of its abstract quotient with all
reduced expansions is needed", tex 9644–9646): a vector of `Λ` whose reduced expansion vanishes
lies in `𝔪Λ`. Only the bridge to lane RC0's `ConstituentModelRel` uses it, because that
interface reads the forms in `Λ/𝔪Λ`. Kind: definition (bridge hypothesis). -/
def Saturated : Prop :=
  ∀ v : X.Λ, X.redE v = 0 → (v : X.I → X.K) ∈ (X.m • ⊤ : Submodule X.O X.Λ).map X.Λ.subtype

/-- **`𝔪Λ` reduces to zero** (the converse of saturation, always true). Kind: PROVED (the
reduced expansions are annihilated by `𝔪`). -/
theorem le_ker_redE : (X.m • ⊤ : Submodule X.O X.Λ) ≤ LinearMap.ker X.redE :=
  le_ker_redExpOf X.m X.expand

end GaloisConstituentModel

/-- **RC2's rules within a budget from a constituent model over `G_ℚ`** (the odd source at one
stage). Kind: PROVED (`GaloisTraceModel.rulesUpTo_of_model`). -/
theorem rulesUpTo_of_galoisConstituents {T : TypeData L ε} {R : Finset ℕ → ZMod 2}
    {ap : ℕ → ℤ} {chiType : GalQ →* Multiplicative L} {W : ℕ}
    (X : GaloisConstituentModel T R ap (W + 1) chiType) (hI : X.Inputs)
    (htyp : IsTypeChar T chiType) (hap : ApEven T ap) : RulesUpTo ε (symb T R) W :=
  GaloisTraceModel.rulesUpTo_of_model (X.toGaloisTraceModel hI) htyp hap

/-- **RC2's coefficient rules from constituent models at every budget** (the even source). Kind:
PROVED (`coefficientRules_of_galois`). -/
theorem coefficientRules_of_galoisConstituents {T : TypeData L ε} {R : Finset ℕ → ZMod 2}
    {ap : ℕ → ℤ} {chiType : GalQ →* Multiplicative L}
    (X : ∀ B, GaloisConstituentModel T R ap B chiType) (hI : ∀ B, (X B).Inputs)
    (htyp : IsTypeChar T chiType) (hap : ApEven T ap) : CoefficientRules ε (symb T R) :=
  coefficientRules_of_galois (fun B => (X B).toGaloisTraceModel (hI B)) htyp hap

/-! ## Constituent models with zero forms -/

section ZeroForms

variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]

/-- **A constituent model of the zero reading on given constituent representations** (the zero
forms `F_U = 0`, the zero functionals). It is built from
* `FrobeniusExists` and a type character reading the types;
* a coefficient ring with `2 ∈ 𝔪`;
* representations `ρ` of `G_ℚ` and a lattice `Λ` preserved by their scalar traces and
  determinants;
* an integral expansion of `Λ`, with the operators preserving coefficientwise congruences.

The fields about `U` hold at every `U`: the reduced trace orbit of the zero forms is constant, so
`N_U` is the common kernel of the characters (`mem_consN_of_const`). Kind: PROVED. -/
def GaloisConstituentModel.zeroForms (hFrob : FrobeniusExists) (T : TypeData L ε) (ap : ℕ → ℤ)
    (B : ℕ) (chiType : GalQ →* Multiplicative L) (htyp : IsTypeChar T chiType) (m : Ideal O)
    (two_mem : (2 : O) ∈ m) (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (stable_t : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) (stable_d : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ)
    {C : Type} (coefK : (I → K) →ₗ[K] (C → K)) (expand : Λ →ₗ[O] (C → O))
    (expand_spec : ∀ (v : Λ) (n : C), algebraMap O K (expand v n) = coefK v n)
    (cong_t : ∀ g (v : Λ), redExpOf m expand v = 0 →
      redExpOf m expand (latT ρ Λ stable_t g v) = 0)
    (cong_d : ∀ g (v : Λ), redExpOf m expand v = 0 →
      redExpOf m expand (latD ρ Λ stable_d g v) = 0) :
    GaloisConstituentModel T (fun _ => 0) ap B chiType where
  I := I
  K := K
  O := O
  m := m
  two_mem := two_mem
  ρ := ρ
  Λ := Λ
  stable_t := stable_t
  stable_d := stable_d
  C := C
  coefK := coefK
  expand := expand
  expand_spec := expand_spec
  cong_t := cong_t
  cong_d := cong_d
  F _ := 0
  read _ := 0
  frob := chooseFrob hFrob
  frob_spec _ hq := chooseFrob_spec hFrob hq.1
  det_orbit _ _ _ _ _ := by simp only [map_zero]
  two_fresh _ _ _ _ _ := by simp only [map_zero]
  kummer _ _ _ _ h1 h2 := Subgroup.mem_sup_right
    ((mem_consN_of_const (fun g U => by simp only [redTrace, map_zero])).mpr ⟨h1, h2⟩)
  finiteIndex U _ _ := by
    have := finite_of_typeData T
    exact consN_const_finiteIndex (fun g U => by simp only [redTrace, map_zero]) U
  chebotarev U hU _ g avoid :=
    consN_const_chebotarev T htyp (fun g U => by simp only [redTrace, map_zero])
      (fun _ hq => chooseFrob_spec hFrob hq.1) U hU g avoid

variable (hFrob : FrobeniusExists) (T : TypeData L ε) (ap : ℕ → ℤ) (B : ℕ)
  (chiType : GalQ →* Multiplicative L) (htyp : IsTypeChar T chiType) (m : Ideal O)
  (two_mem : (2 : O) ∈ m) (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K))
  (stable_t : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) (stable_d : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ)
  {C : Type} (coefK : (I → K) →ₗ[K] (C → K)) (expand : Λ →ₗ[O] (C → O))
  (expand_spec : ∀ (v : Λ) (n : C), algebraMap O K (expand v n) = coefK v n)
  (cong_t : ∀ g (v : Λ), redExpOf m expand v = 0 →
    redExpOf m expand (latT ρ Λ stable_t g v) = 0)
  (cong_d : ∀ g (v : Λ), redExpOf m expand v = 0 →
    redExpOf m expand (latD ρ Λ stable_d g v) = 0)

attribute [local instance] GaloisConstituentModel.modMexp

/-- The functionals of a zero-forms model vanish. Kind: PROVED (definition). -/
theorem GaloisConstituentModel.zeroForms_readE (U : Finset ℕ)
    (x : (GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp m two_mem ρ Λ stable_t
      stable_d coefK expand expand_spec cong_t cong_d).Mexp) :
    (GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp m two_mem ρ Λ stable_t
      stable_d coefK expand expand_spec cong_t cong_d).readE U x = 0 :=
  rfl

/-- **The inputs of a zero-forms model hold**: every reading is zero; in (O.12) the elements
`τ, φ` have the prescribed characters by `chi_surj` at the good set `U`. Kind: PROVED. -/
theorem GaloisConstituentModel.zeroForms_inputs :
    (GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp m two_mem ρ Λ stable_t
      stable_d coefK expand expand_spec cong_t cong_d).Inputs := by
  set X := GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp m two_mem ρ Λ stable_t
    stable_d coefK expand expand_spec cong_t cong_d
  refine ⟨fun U q _ _ _ _ => (GaloisConstituentModel.zeroForms_readE hFrob T ap B chiType htyp m
    two_mem ρ Λ stable_t stable_d coefK expand expand_spec cong_t cong_d U _).symm,
    fun U p hpU hU _ g => ?_⟩
  obtain ⟨τ, hτT, hτB⟩ := X.chi_surj htyp U hU 0 (fun s => if s = p then 1 else 0)
  obtain ⟨φ, hφT, hφB⟩ := X.chi_surj htyp U hU (T.typ p) (fun s => legBit p s)
  refine ⟨τ, φ, 1, Or.inl rfl, by rw [hτT, ofAdd_zero], fun s hs hsp => ?_, ?_, hφT,
    fun s hs _ => hφB s hs, ?_⟩
  · rw [hτB s hs, if_neg' hsp, ofAdd_zero]
  · rw [hτB p hpU, if_pos' rfl]
  · change _ * (0 : ZMod 2) - _ * (0 : ZMod 2) = (0 : ZMod 2) - 0
    simp

/-- **A zero-forms model satisfies the unbudgeted forms** (no tex line). Kind: PROVED. -/
theorem GaloisConstituentModel.zeroForms_unbudgeted :
    (GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp m two_mem ρ Λ stable_t
      stable_d coefK expand expand_spec cong_t cong_d).Unbudgeted :=
  GaloisConstituentModel.unbudgeted_of_forms_eq_zero _ (fun _ => rfl) htyp

end ZeroForms

/-! ## Non-vacuity: one constituent with the genuine `2`-adic Tate representation -/

section Tate

open ZInQ.Manuscript.RC.TateWiring

/-- `2 ∈ 𝔪_{ℤ₂}`. Kind: PROVED (`𝔪_{ℤ₂} = (2)`). -/
theorem two_mem_maximalIdeal_padicInt : (2 : ℤ_[2]) ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact_mod_cast Ideal.mem_span_singleton_self ((2 : ℕ) : ℤ_[2])

/-- **The lattice of integral vectors** `{v : Unit → ℚ₂ | v () ∈ ℤ₂}`. Kind: definition. -/
def intLattice : Submodule ℤ_[2] (Unit → ℚ_[2]) := Submodule.pi Set.univ fun _ => 1

/-- Membership in the lattice of integral vectors. Kind: PROVED. -/
theorem mem_intLattice {v : Unit → ℚ_[2]} :
    v ∈ intLattice ↔ ∀ i, ∃ a : ℤ_[2], (a : ℚ_[2]) = v i := by
  simp only [intLattice, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one,
    PadicInt.algebraMap_apply]

/-- The coordinate of an integral vector has norm at most one. Kind: PROVED. -/
theorem norm_le_one_of_mem_intLattice (v : intLattice) (i : Unit) :
    ‖(v : Unit → ℚ_[2]) i‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := mem_intLattice.mp v.2 i
  rw [← ha, ← PadicInt.norm_def]
  exact PadicInt.norm_le_one a

/-- **The integral coordinate** of a vector of the integral lattice, the Fourier expansion of
the one-constituent model (`C = Unit`). Kind: definition. -/
def intCoord : intLattice →ₗ[ℤ_[2]] (Unit → ℤ_[2]) where
  toFun v i := Padic.lift ((v : Unit → ℚ_[2]) i) (norm_le_one_of_mem_intLattice v i)
  map_add' v w := by
    funext i
    apply PadicInt.ext
    rfl
  map_smul' r v := by
    funext i
    apply PadicInt.ext
    rfl

/-- Kind: PROVED (definition). -/
theorem intCoord_coe (v : intLattice) (i : Unit) :
    ((intCoord v i : ℤ_[2]) : ℚ_[2]) = (v : Unit → ℚ_[2]) i := rfl

/-- The integral coordinate is the coordinate (`expand_spec` of the one-constituent model).
Kind: PROVED. -/
theorem intCoord_spec (v : intLattice) (n : Unit) :
    algebraMap ℤ_[2] ℚ_[2] (intCoord v n) = (LinearMap.id : (Unit → ℚ_[2]) →ₗ[ℚ_[2]] _) v n := by
  rw [PadicInt.algebraMap_apply, intCoord_coe]
  rfl

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **The `2`-adic Tate representation of `E` with values in `GL₂(ℚ₂)`**: lane RC17's
`rhoGL E` composed with `ℤ₂ ⊂ ℚ₂`. Kind: definition. -/
def tateRhoQ : GalQ →* GL (Fin 2) ℚ_[2] :=
  (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := 2))).comp (rhoGL E)

/-- Kind: PROVED (definition). -/
theorem coe_tateRhoQ (σ : GalQ) :
    ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]) =
      (tateMatrix E σ).map (PadicInt.Coe.ringHom (p := 2)) :=
  rfl

/-- **The trace of `tateRhoQ E σ` is the trace of `ρ_T(σ)` on `T₂E`.** Kind: PROVED. -/
theorem trace_tateRhoQ (σ : GalQ) :
    ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]).trace =
      ((LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 σ) : ℤ_[2]) : ℚ_[2]) := by
  rw [coe_tateRhoQ, ← trace_tateMatrix]
  exact (AddMonoidHom.map_trace (PadicInt.Coe.ringHom (p := 2)) (tateMatrix E σ)).symm

/-- **The determinant of `tateRhoQ E σ` is the determinant of `ρ_T(σ)` on `T₂E`.** Kind:
PROVED. -/
theorem det_tateRhoQ (σ : GalQ) :
    ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]).det =
      ((LinearMap.det (tateRep E 2 σ) : ℤ_[2]) : ℚ_[2]) := by
  rw [coe_tateRhoQ, ← det_tateMatrix]
  exact (RingHom.map_det (PadicInt.Coe.ringHom (p := 2)) (tateMatrix E σ)).symm

/-- **The integral lattice is preserved by the scalar trace of the Tate representation.** Kind:
PROVED. -/
theorem tate_stable_t (g : GalQ) (v : Unit → ℚ_[2]) (hv : v ∈ intLattice) :
    tV (fun _ : Unit => tateRhoQ E) g v ∈ intLattice := by
  rw [mem_intLattice] at hv ⊢
  intro i
  obtain ⟨a, ha⟩ := hv i
  refine ⟨LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 g) * a, ?_⟩
  simp only [tV, scalarOp_apply, trace_tateRhoQ, PadicInt.coe_mul, ha]

/-- **The integral lattice is preserved by the determinant of the Tate representation.** Kind:
PROVED. -/
theorem tate_stable_d (g : GalQ) (v : Unit → ℚ_[2]) (hv : v ∈ intLattice) :
    dV (fun _ : Unit => tateRhoQ E) g v ∈ intLattice := by
  rw [mem_intLattice] at hv ⊢
  intro i
  obtain ⟨a, ha⟩ := hv i
  refine ⟨LinearMap.det (tateRep E 2 g) * a, ?_⟩
  simp only [dV, scalarOp_apply, det_tateRhoQ, PadicInt.coe_mul, ha]

/-- The coordinate of `t(g) v` is the trace of `ρ_T(g)` times the coordinate of `v`. Kind:
PROVED. -/
theorem intCoord_latT (g : GalQ) (v : intLattice) (i : Unit) :
    intCoord (latT (fun _ : Unit => tateRhoQ E) intLattice (tate_stable_t E) g v) i =
      LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 g) * intCoord v i := by
  apply PadicInt.ext
  rw [PadicInt.coe_mul, intCoord_coe, intCoord_coe, latT_coe]
  simp only [tV, scalarOp_apply, trace_tateRhoQ]

/-- The coordinate of `d(g) v` is the determinant of `ρ_T(g)` times the coordinate of `v`. Kind:
PROVED. -/
theorem intCoord_latD (g : GalQ) (v : intLattice) (i : Unit) :
    intCoord (latD (fun _ : Unit => tateRhoQ E) intLattice (tate_stable_d E) g v) i =
      LinearMap.det (tateRep E 2 g) * intCoord v i := by
  apply PadicInt.ext
  rw [PadicInt.coe_mul, intCoord_coe, intCoord_coe, latD_coe]
  simp only [dV, scalarOp_apply, det_tateRhoQ]

/-- **The scalar traces preserve coefficientwise congruences** (multiplication by an integral
scalar). Kind: PROVED. -/
theorem tate_cong_t (g : GalQ) (v : intLattice)
    (hv : redExpOf (IsLocalRing.maximalIdeal ℤ_[2]) intCoord v = 0) :
    redExpOf (IsLocalRing.maximalIdeal ℤ_[2]) intCoord
      (latT (fun _ : Unit => tateRhoQ E) intLattice (tate_stable_t E) g v) = 0 := by
  funext i
  have h := congrFun hv i
  rw [redExpOf_apply] at h ⊢
  rw [intCoord_latT, map_mul, h]
  exact mul_zero _

/-- **The determinants preserve coefficientwise congruences.** Kind: PROVED. -/
theorem tate_cong_d (g : GalQ) (v : intLattice)
    (hv : redExpOf (IsLocalRing.maximalIdeal ℤ_[2]) intCoord v = 0) :
    redExpOf (IsLocalRing.maximalIdeal ℤ_[2]) intCoord
      (latD (fun _ : Unit => tateRhoQ E) intLattice (tate_stable_d E) g v) = 0 := by
  funext i
  have h := congrFun hv i
  rw [redExpOf_apply] at h ⊢
  rw [intCoord_latD, map_mul, h]
  exact mul_zero _

/-- The integral vector `1`. Kind: definition. -/
def intOne : intLattice := ⟨fun _ => 1, mem_intLattice.mpr fun _ => ⟨1, PadicInt.coe_one⟩⟩

/-- **The reduced expansions of the integral lattice form a nonzero module** (the reduced
coordinate of `1` is `1 ≠ 0` in `ℤ₂/𝔪`). Kind: PROVED. -/
theorem intLattice_exp_nontrivial :
    Nontrivial (LinearMap.range (redExpOf (IsLocalRing.maximalIdeal ℤ_[2]) intCoord)) := by
  refine ⟨⟨⟨_, LinearMap.mem_range_self _ intOne⟩, 0, fun h => ?_⟩⟩
  have h1 := congrFun (congrArg Subtype.val h) ()
  change redExpOf (IsLocalRing.maximalIdeal ℤ_[2]) intCoord intOne () = 0 at h1
  rw [redExpOf_apply] at h1
  have hone : intCoord intOne () = 1 := PadicInt.ext rfl
  rw [hone] at h1
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp h1
  exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one hmem

/-- **The integral lattice is saturated** (`ℤ₂` is a DVR and the lattice has rank one): a vector
with vanishing reduced coordinate lies in `𝔪Λ`. Kind: PROVED. -/
theorem intLattice_saturated (v : intLattice)
    (hv : redExpOf (IsLocalRing.maximalIdeal ℤ_[2]) intCoord v = 0) :
    (v : Unit → ℚ_[2]) ∈
      (IsLocalRing.maximalIdeal ℤ_[2] • ⊤ : Submodule ℤ_[2] intLattice).map intLattice.subtype := by
  have h := congrFun hv ()
  rw [redExpOf_apply] at h
  have ha := Ideal.Quotient.eq_zero_iff_mem.mp h
  have hv' : v = intCoord v () • intOne := by
    apply Subtype.ext
    funext i
    show (v : Unit → ℚ_[2]) i = (intCoord v () • (intOne : Unit → ℚ_[2])) i
    rw [Pi.smul_apply, Algebra.smul_def, PadicInt.algebraMap_apply, intCoord_coe]
    simp [intOne]
  refine ⟨v, ?_, rfl⟩
  rw [hv']
  exact Submodule.smul_mem_smul ha Submodule.mem_top

variable (hFrob : FrobeniusExists)

/-- **Non-vacuity of `GaloisConstituentModel` with a genuine Galois representation**, for every
type data and every type character reading the types. For an elliptic curve `E/ℚ`, given
`FrobeniusExists`, it is the constituent model with the following data:
* ONE constituent (`I = Unit`), whose representation is the `2`-adic Tate representation of `E`;
* `K = ℚ₂`, `O = ℤ₂`, `𝔪` the maximal ideal of `ℤ₂`;
* `Λ` the lattice of integral vectors, with Fourier expansion its coordinate (`C = Unit`);
* the zero forms and the zero functionals.

The operators preserve `Λ` and coefficientwise congruences (`tate_stable_t`, `tate_cong_t`), and
the module of reduced expansions is nonzero (`tateConstituentModelOf_nontrivial`). The
constituents of the actual forms `F_U = θ H_U` are weight-two cuspidal newforms and Eisenstein
character pairs (tex 9647–9654, 9762–9771), not `E` or its twists. Kind: PROVED. -/
def tateConstituentModelOf (T : TypeData L ε) (chiType : GalQ →* Multiplicative L)
    (htyp : IsTypeChar T chiType) (ap : ℕ → ℤ) (B : ℕ) :
    GaloisConstituentModel T (fun _ => 0) ap B chiType :=
  GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp (IsLocalRing.maximalIdeal ℤ_[2])
    two_mem_maximalIdeal_padicInt (fun _ : Unit => tateRhoQ E) intLattice (tate_stable_t E)
    (tate_stable_d E) LinearMap.id intCoord intCoord_spec (tate_cong_t E) (tate_cong_d E)

section Of

variable (T : TypeData L ε) (chiType : GalQ →* Multiplicative L) (htyp : IsTypeChar T chiType)
  (ap : ℕ → ℤ) (B : ℕ)

/-- The constituent representation of `tateConstituentModelOf` is the Tate representation of
`E`. Kind: PROVED (definition). -/
theorem tateConstituentModelOf_ρ :
    (tateConstituentModelOf E hFrob T chiType htyp ap B).ρ () = tateRhoQ E :=
  rfl

/-- **The data of `tateConstituentModelOf`**: one constituent, `K = ℚ₂`, `O = ℤ₂`, `𝔪` the
maximal ideal of `ℤ₂`, `Λ` the lattice of integral vectors with its coordinate as expansion,
zero forms and zero functionals. Kind: PROVED (definition). -/
theorem tateConstituentModelOf_data :
    (tateConstituentModelOf E hFrob T chiType htyp ap B).I = Unit ∧
      (tateConstituentModelOf E hFrob T chiType htyp ap B).K = ℚ_[2] ∧
      (tateConstituentModelOf E hFrob T chiType htyp ap B).O = ℤ_[2] ∧
      (tateConstituentModelOf E hFrob T chiType htyp ap B).m = IsLocalRing.maximalIdeal ℤ_[2] ∧
      (tateConstituentModelOf E hFrob T chiType htyp ap B).Λ = intLattice ∧
      (tateConstituentModelOf E hFrob T chiType htyp ap B).C = Unit ∧
      (∀ U, (tateConstituentModelOf E hFrob T chiType htyp ap B).F U = 0) ∧
      (∀ U, (tateConstituentModelOf E hFrob T chiType htyp ap B).read U = 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- The scalar trace operator of `tateConstituentModelOf` is multiplication by the trace of
`ρ_T(σ)` on `T₂E`. Kind: PROVED (`trace_tateRhoQ`). -/
theorem tateConstituentModelOf_tV (σ : GalQ) (v : Unit → ℚ_[2]) :
    tV (tateConstituentModelOf E hFrob T chiType htyp ap B).ρ σ v () =
      ((LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 σ) : ℤ_[2]) : ℚ_[2]) * v () := by
  show ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]).trace * v () = _
  rw [trace_tateRhoQ]

/-- The determinant operator of `tateConstituentModelOf` is multiplication by the determinant of
`ρ_T(σ)` on `T₂E`. Kind: PROVED (`det_tateRhoQ`). -/
theorem tateConstituentModelOf_dV (σ : GalQ) (v : Unit → ℚ_[2]) :
    dV (tateConstituentModelOf E hFrob T chiType htyp ap B).ρ σ v () =
      ((LinearMap.det (tateRep E 2 σ) : ℤ_[2]) : ℚ_[2]) * v () := by
  show ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]).det * v () = _
  rw [det_tateRhoQ]

/-- The inputs of `tateConstituentModelOf` hold. Kind: PROVED (`zeroForms_inputs`). -/
theorem tateConstituentModelOf_inputs :
    (tateConstituentModelOf E hFrob T chiType htyp ap B).Inputs :=
  GaloisConstituentModel.zeroForms_inputs hFrob _ ap B _ _ _ _ _ _ _ _ _ _ _ _ _

/-- `tateConstituentModelOf` satisfies the unbudgeted forms (its forms are zero; no tex line).
Kind: PROVED (`zeroForms_unbudgeted`). -/
theorem tateConstituentModelOf_unbudgeted :
    (tateConstituentModelOf E hFrob T chiType htyp ap B).Unbudgeted :=
  GaloisConstituentModel.zeroForms_unbudgeted hFrob _ ap B _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **The module of reduced expansions of the Tate constituent model is nonzero** (it is
`ℤ₂/𝔪`, on which `t(σ)` is the reduction of the trace of `ρ_T(σ)`). Kind: PROVED
(`intLattice_exp_nontrivial`). -/
theorem tateConstituentModelOf_nontrivial :
    Nontrivial (tateConstituentModelOf E hFrob T chiType htyp ap B).Mexp :=
  intLattice_exp_nontrivial

/-- **The Tate constituent model is saturated** (the bridge hypothesis of lane RC0's interface
holds here; no tex line). Kind: PROVED (`intLattice_saturated`). -/
theorem tateConstituentModelOf_saturated :
    (tateConstituentModelOf E hFrob T chiType htyp ap B).Saturated :=
  intLattice_saturated

end Of

variable (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m) (ap : ℕ → ℤ) (B : ℕ)

/-- **The Tate constituent model over the genuine type data** `typeData m`, with the genuine type
character `typChar m`. The Tate representation of `E` only shows that the structure is inhabited
by a genuine Galois representation. Kind: PROVED. -/
def tateConstituentModel :
    GaloisConstituentModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  tateConstituentModelOf E hFrob (typeData m hm h4) (typChar m) (isTypeChar_typeData m hm h4) ap B

/-- Kind: PROVED (definition). -/
theorem tateConstituentModel_ρ :
    (tateConstituentModel E hFrob m hm h4 ap B).ρ () = tateRhoQ E :=
  rfl

/-- The inputs of `tateConstituentModel` hold. Kind: PROVED. -/
theorem tateConstituentModel_inputs : (tateConstituentModel E hFrob m hm h4 ap B).Inputs :=
  tateConstituentModelOf_inputs E hFrob _ _ _ ap B

/-- `tateConstituentModel` satisfies the unbudgeted forms (no tex line). Kind: PROVED. -/
theorem tateConstituentModel_unbudgeted :
    (tateConstituentModel E hFrob m hm h4 ap B).Unbudgeted :=
  tateConstituentModelOf_unbudgeted E hFrob _ _ _ ap B

/-- `tateConstituentModel` is saturated (no tex line). Kind: PROVED. -/
theorem tateConstituentModel_saturated :
    (tateConstituentModel E hFrob m hm h4 ap B).Saturated :=
  tateConstituentModelOf_saturated E hFrob _ _ _ ap B

/-- **The genuine Galois trace model of the Tate constituent model** over `typeData m`: the
nonzero module of reduced expansions with the induced scalar traces and determinants of `ρ_T`.
Kind: PROVED (`toGaloisTraceModel`). -/
def tateGaloisTraceModel : GaloisTraceModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  (tateConstituentModel E hFrob m hm h4 ap B).toGaloisTraceModel
    (tateConstituentModel_inputs E hFrob m hm h4 ap B)

/-- **The module of `tateGaloisTraceModel` is nonzero.** Kind: PROVED. -/
theorem tateGaloisTraceModel_nontrivial :
    Nontrivial (tateGaloisTraceModel E hFrob m hm h4 ap B).M :=
  intLattice_exp_nontrivial

/-- **The Tate constituent model over stage type data**, with the stage type character
`stageChar m₁ ℓ₀`. Kind: PROVED. -/
def tateConstituentModelStage {m₁ ℓ₀ : ℕ} [NeZero m₁] {ε₁ : SqClass m₁ × ZMod 2 →+ ZMod 2}
    (T : TypeData (SqClass m₁ × ZMod 2) ε₁) (hTm : T.m = m₁ * ℓ₀)
    (hTtyp : ∀ p : ℕ, T.typ p = (sqClassOf m₁ p, legBit p ℓ₀)) (hℓ₀ : ℓ₀.Prime) (hℓ₀2 : ℓ₀ ≠ 2) :
    GaloisConstituentModel T (fun _ => 0) ap B (stageChar m₁ ℓ₀) :=
  tateConstituentModelOf E hFrob T (stageChar m₁ ℓ₀) (isTypeChar_stage T hTm hTtyp hℓ₀ hℓ₀2) ap B

end Tate

/-- **The readings of the Tate constituent models compose**: the coefficient rules for the zero
symbol over `typeData m`. Kind: PROVED. -/
theorem coefficientRules_tate (E : WeierstrassCurve ℚ) [E.IsElliptic] (hFrob : FrobeniusExists)
    (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m) :
    CoefficientRules (signChar m h4) (symb (typeData m hm h4) (fun _ => 0)) :=
  coefficientRules_of_galoisConstituents
    (fun B => tateConstituentModel E hFrob m hm h4 (fun _ => 0) B)
    (fun B => tateConstituentModel_inputs E hFrob m hm h4 (fun _ => 0) B)
    (isTypeChar_typeData m hm h4) (fun _ _ => ⟨0, (add_zero 0).symm⟩)

/-! ### The case `E = E_ℓ` -/

section Ecurve

variable (hFrob : FrobeniusExists) {ℓ : ℕ} (hℓ : 0 < ℓ) (m : ℕ) [NeZero m] (hm : 0 < m)
  (h4 : 4 ∣ m) (ap : ℕ → ℤ) (B : ℕ)

/-- **The Tate constituent model of `E_ℓ`** over the genuine type data `typeData m`. Kind:
PROVED. -/
def tateConstituentModelEcurve :
    GaloisConstituentModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  @tateConstituentModel (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hFrob m _ hm
    h4 ap B

/-- Kind: PROVED (definition). -/
theorem tateConstituentModelEcurve_ρ :
    (tateConstituentModelEcurve hFrob hℓ m hm h4 ap B).ρ () =
      @tateRhoQ (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) :=
  rfl

/-- The inputs of `tateConstituentModelEcurve` hold. Kind: PROVED. -/
theorem tateConstituentModelEcurve_inputs :
    (tateConstituentModelEcurve hFrob hℓ m hm h4 ap B).Inputs :=
  @tateConstituentModel_inputs (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hFrob
    m _ hm h4 ap B

/-- `tateConstituentModelEcurve` satisfies the unbudgeted forms (no tex line). Kind: PROVED. -/
theorem tateConstituentModelEcurve_unbudgeted :
    (tateConstituentModelEcurve hFrob hℓ m hm h4 ap B).Unbudgeted :=
  @tateConstituentModel_unbudgeted (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ)
    hFrob m _ hm h4 ap B

/-- The genuine Galois trace model of `tateConstituentModelEcurve`. Kind: PROVED. -/
def tateGaloisTraceModelEcurve :
    GaloisTraceModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  @tateGaloisTraceModel (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hFrob m _ hm
    h4 ap B

end Ecurve

/-! ### Unconditional forms (`FrobeniusExists` is proved, `frobeniusExists`) -/

section Unconditional

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m)
  (ap : ℕ → ℤ) (B : ℕ)

/-- **The Tate constituent model over `typeData m`, with no hypothesis** (`frobeniusExists`).
The Tate representation of `E` only shows that the structure is inhabited by a genuine Galois
representation. Kind: PROVED. -/
def tateConstituentModel' :
    GaloisConstituentModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  tateConstituentModel E frobeniusExists m hm h4 ap B

/-- Kind: PROVED (definition). -/
theorem tateConstituentModel'_ρ : (tateConstituentModel' E m hm h4 ap B).ρ () = tateRhoQ E :=
  rfl

/-- The inputs of `tateConstituentModel'` hold. Kind: PROVED. -/
theorem tateConstituentModel'_inputs : (tateConstituentModel' E m hm h4 ap B).Inputs :=
  tateConstituentModel_inputs E frobeniusExists m hm h4 ap B

/-- `tateConstituentModel'` satisfies the unbudgeted forms (`F = 0`; no tex line). Kind:
PROVED. -/
theorem tateConstituentModel'_unbudgeted : (tateConstituentModel' E m hm h4 ap B).Unbudgeted :=
  tateConstituentModel_unbudgeted E frobeniusExists m hm h4 ap B

/-- `tateConstituentModel'` is saturated (no tex line). Kind: PROVED. -/
theorem tateConstituentModel'_saturated : (tateConstituentModel' E m hm h4 ap B).Saturated :=
  tateConstituentModel_saturated E frobeniusExists m hm h4 ap B

/-- The module of reduced expansions of `tateConstituentModel'` is nonzero. Kind: PROVED. -/
theorem tateConstituentModel'_nontrivial :
    Nontrivial (tateConstituentModel' E m hm h4 ap B).Mexp :=
  intLattice_exp_nontrivial

end Unconditional

/-- **The coefficient rules for the zero symbol from the Tate constituent models, with no
hypothesis.** Kind: PROVED. -/
theorem coefficientRules_tate' (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) [NeZero m]
    (hm : 0 < m) (h4 : 4 ∣ m) :
    CoefficientRules (signChar m h4) (symb (typeData m hm h4) (fun _ => 0)) :=
  coefficientRules_tate E frobeniusExists m hm h4

section UnconditionalEcurve

variable {ℓ : ℕ} (hℓ : 0 < ℓ) (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m) (ap : ℕ → ℤ) (B : ℕ)

/-- **The Tate constituent model of `E_ℓ` over `typeData m`, with no hypothesis.** Kind:
PROVED. -/
def tateConstituentModelEcurve' :
    GaloisConstituentModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  tateConstituentModelEcurve frobeniusExists hℓ m hm h4 ap B

/-- The inputs of `tateConstituentModelEcurve'` hold. Kind: PROVED. -/
theorem tateConstituentModelEcurve'_inputs :
    (tateConstituentModelEcurve' hℓ m hm h4 ap B).Inputs :=
  tateConstituentModelEcurve_inputs frobeniusExists hℓ m hm h4 ap B

/-- `tateConstituentModelEcurve'` satisfies the unbudgeted forms (no tex line). Kind: PROVED. -/
theorem tateConstituentModelEcurve'_unbudgeted :
    (tateConstituentModelEcurve' hℓ m hm h4 ap B).Unbudgeted :=
  tateConstituentModelEcurve_unbudgeted frobeniusExists hℓ m hm h4 ap B

end UnconditionalEcurve

end ZInQ.Manuscript.RC.AddressGenuine
