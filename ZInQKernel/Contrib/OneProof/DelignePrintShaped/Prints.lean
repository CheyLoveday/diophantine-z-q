import ZInQKernel.Contrib.OneProof.Y3HodgePrint

/-! # The row `deligneCanonicalModelY3EveryPrint`: print-shaped statements

The open row `Y3Hodge.DeligneCanonicalModelY3EveryPrint` is Shimura's Main Theorem I for `Y₃` (the quaternion
algebra `B = (2, −3 | ℚ)` of discriminant 6, its maximal order `𝒪`, full level `K₃ = {k ∈ 𝒪̂^× : k ≡ 1 mod 3}`),
stated for every witness of the polarization-free fine moduli problem `Y3Fix.R1fpPropsAbP`. This file states, over
the kernel's types, the refereed statements it is to be reduced to, each as the printed statement or weaker:

* `VoightQMComplexModuliPrint` (T2a): the complex moduli of QM abelian surfaces in lattice form, at level 1
  (J. Voight, *Quaternion Algebras*, GTM 288, §43.6);
* `CornutVatsalCMReciprocityPrint` (T2b): the complex uniformization of Shimura's canonical model at level `K₃`
  and the reciprocity law at CM points (C. Cornut, V. Vatsal, Doc. Math. 10 (2005), §3.1.1, Lemmas 3.7 and 3.11);
* `FineModuliCanonicalModelGlue` (W-a, **GLUE**, not a print): the fine moduli `ℚ`-scheme at `K₃`, with its moduli
  uniformization, is Shimura's canonical model;
* `BoutotCarayolModuliPrint` (T2c): the moduli scheme of the polarization-free problem at level `U(3) = K₃` and its
  complex points (J.-F. Boutot, H. Carayol, Astérisque 196–197 (1991), Ch. III, §§0–1);
* `BoutotCarayolPolarizationPrint` (T2c′): the principal *-polarization of a complex QM surface (the same,
  Proposition 1.5), in the Riemann-form terms of `HasPrincipalRiemannMu`.

The moduli description of the point `[z, g]` (`IsLevelPoint`) is defined here in lattice form; the level-3 marking
of `ℂ²/Λ_τ` is computed in the companion file. No new structure is introduced: every statement quantifies over the
kernel's `PkgI3.AbVar ℂ`, `LeafQM.AV.QMStr`, `LeafQM.AV.QML3`, `LeafQM.AV.M3`, the moduli bijections `PtEquiv`,
the kernel's uniformizations `ZInQ.LeafPush2.IsUniformization`, and the adelic objects of `ShimuraCFT`.
-/

set_option autoImplicit false

noncomputable section

namespace DelignePS

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open ShimuraCFT RayClassCFT
open NumberField IsDedekindDomain TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization)
open HDec.HSyn.G0Split.FibreQM (qmMat IotaCompatible)
open Y3Hodge (HPM DCRelPM toPM)

/-! ## 1. The complex QM torus `(A_τ, ι_τ)` and the moduli description of `[z, g]` -/

/-- **`(A, ι) ≅ (A_τ, ι_τ)`** (Voight 43.6.12: `Λ_τ = ι_∞(𝒪)(τ;1) ⊂ ℂ²`, `A_τ = ℂ²/Λ_τ`, `ι_τ` induced by `ι_∞`):
an analytic uniformization `Φu : ℂ² → A(ℂ)` with kernel `Λ_τ = ι(𝒪)(τ, 1)ᵀ` (the kernel's `IsUniformization`:
holomorphic homomorphism, onto, kernel exactly `Λ_τ`) which is `𝒪`-equivariant: `Φu(ι(a) v) = ι_A(a)(Φu v)`. -/
def IsQMTorusAt (A : PkgI3.AbVar ℂ) (q : QMStr A) (τ : UpperHalfPlane) : Prop :=
  ∃ Φu : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
    ∀ (a : O) (z : Fin 2 → ℂ), Φu ((qmMat a).mulVec z) = Φu z ≫ (q.iota a).hom

/-- **A principal polarization of type `μ` on `(A, ι)`, as a Riemann form** (Voight §43.4: a polarization of a
complex torus is a Riemann form, Definition 43.4.14, principal as in Definition 43.4.16; Definitions 43.6.4, 43.6.9:
the Rosati involution `†` satisfies `ι(α)† = ι(α*)`, `α* = μ⁻¹ ᾱ μ`; Boutot–Carayol III.1.5: a principal
*-polarization), read on a uniformization `e : ℂⁿ → A(ℂ)` with kernel `Λ` (the kernel's `IsUniformization`):
`E : ℂⁿ × ℂⁿ → ℝ` real bilinear, integral on `Λ`, alternating, `E(iv, iw) = E(v, w)`, `E(iv, v) > 0` for `v ≠ 0`,
unimodular on `Λ` (every `ℤ`-linear form on `Λ` is `E(·, w)`, `w ∈ Λ`), and for every `a ∈ 𝒪` the analytic lifts
`M_a`, `M_{a*}` of `ι(a)`, `ι(a*)` are adjoint for `E` (`a* = Y3Hodge.dagO a = μ⁻¹ ā μ`, `μ = 2j + ij`, `μ² = −6`).
`n` and `Λ` are existential but forced (background): if the kernel of `e` contained a complex line `ℂv ⊂ Λ`, then
`t E(iv, v)` would be an integer for every real `t`, which positivity rules out; so `n = dim A`, `Λ` is a full
lattice, and the lifts of endomorphisms exist and are unique, so the lift clause is not vacuous. For T2a this is
Voight's own notion (a complex torus with a principal Riemann form); for T2c′ the passage from an algebraic
polarization of `A/ℂ` to a Riemann form is the Appell–Humbert theorem (Mumford, *Abelian varieties*, §§2–3;
background). -/
def HasPrincipalRiemannMu (A : PkgI3.AbVar ℂ) (q : QMStr A) : Prop :=
  ∃ (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ)) (e : (Fin n → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) Λ e ∧
    ∃ E : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ,
      (∀ v ∈ Λ, ∀ w ∈ Λ, ∃ m : ℤ, E v w = m) ∧
      (∀ v, E v v = 0) ∧
      (∀ v w, E (Complex.I • v) (Complex.I • w) = E v w) ∧
      (∀ v, v ≠ 0 → 0 < E (Complex.I • v) v) ∧
      (∀ φ : Λ →+ ℤ, ∃ w ∈ Λ, ∀ v : Λ, E v w = φ v) ∧
      ∀ (a : O) (M M' : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)),
        (∀ z, e (M z) = e z ≫ (q.iota a).hom) → (∀ z, e (M' z) = e z ≫ (q.iota (Y3Hodge.dagO a)).hom) →
        ∀ v w, E (M v) w = E v (M' w)

/-- `w ≡ u⁻¹ (mod 3𝒪̂)`, i.e. `w u ∈ 1 + 3𝒪̂`, for `w ∈ 𝒪` and `u ∈ (B ⊗ 𝔸_f)^×`. -/
def InvModThree (u : BAQˣ) (w : O) : Prop :=
  ∃ y ∈ OhatQ, bEmb (w : B) * (u : BAQ) = 1 + 3 * y

/-- **The object `(ℂ²/Λ_τ, ι_τ, η_w)`**: `P` is uniformized `ι`-compatibly by `Λ_τ`, and its level points are
`η(a) = Φu(ℓ_τ(a w)/3)`, `ℓ_τ(b) = ι(b)(τ, 1)ᵀ`, the `3`-torsion points of `ℂ²/Λ_τ` attached to `a ↦ a w`
(Shimura, J. Math. Soc. Japan 13 (1961), Prop. 4.1: `α ↦ θ_z(α) t₀` is an isomorphism of `𝔬/𝔞` onto the
`𝔞`-torsion `𝔤(𝔞, A_z)`, here with `𝔞 = 3𝔬` and `t₀ = (τ, 1)ᵀ/3`). -/
def IsLevelTorusAt (P : QML3 ℂ) (τ : UpperHalfPlane) (w : O) : Prop :=
  ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧ IotaCompatible P Φu ∧
    ∀ a : O, Additive.toMul (P.e.eta a) =
      Φu ((3 : ℂ)⁻¹ • Y3Fix.ellE τ (BPAnalytic.QM.iota ((a * w : O) : B)))

/-- **The moduli description of the point `[z, g]` of `B^× \ (ℍ^± × (B ⊗ 𝔸_f)^× / K₃)`**: `P` is `(ℂ²/Λ_τ, ι_τ, η_w)`
for a representative `(τ, u)` of the class of `(z, g)` with `τ ∈ ℍ`, `u ∈ 𝒪̂^×`, and `w ≡ u⁻¹ (mod 3)`. This is the
lattice form of the classical description `[h_z, g] ↦ (ℂ²/ι(L_g)(z, 1)ᵀ, ι, level from g)`,
`L_g = B ∩ 𝒪̂ g⁻¹` (`L_u = 𝒪` for `u ∈ 𝒪̂^×`, and `g` acts on the level by right multiplication by `g⁻¹`). -/
def IsLevelPoint (P : QML3 ℂ) (z : HPM) (g : BAQˣ) : Prop :=
  ∃ (τ : UpperHalfPlane) (u : BAQˣ) (w : O), u ∈ OhatU ∧ DCRelPM z g (toPM τ) u ∧ InvModThree u w ∧
    IsLevelTorusAt P τ w

/-! ## 2. T2a: Voight, *Quaternion Algebras*, §43.6 (level 1, over `ℂ`) -/

/-- **T2a (print-shaped): the complex moduli of QM abelian surfaces in lattice form, at level 1.**

*Print.* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021 (open access,
DOI 10.1007/978-3-030-56694-4), §43.6. Setting (§43.6, p. 817; 43.6.12, p. 819): `B` an indefinite quaternion
algebra over `ℚ` of discriminant `D`, `O` a maximal order, `ι_∞ : B ↪ M₂(ℝ)`, `μ ∈ O` with `μ² + D = 0`.
* 43.6.12, p. 819: "Let τ ∈ H². Let Λ_τ := ι_∞(O)(τ;1) ⊂ ℂ². Then Λ_τ is a lattice in ℂ², since rk_ℤ O = 4; let
  A_τ := ℂ²/Λ_τ be the associated complex torus. The map ι_∞ induces a natural injective ring homomorphism
  ι_τ : O → End(A_τ) since ι_∞(O)Λ_τ ⊆ Λ_τ as O itself is closed under multiplication."
* Main Theorem 43.6.14, p. 819: "Let Γ = ι_∞(O¹)/{±1} ⊆ PSL₂(ℝ). Then the map Γ\H² ↔ {(A, ι) principally polarized
  complex abelian surfaces with QM by (O, μ) up to isomorphism}, Γτ ↦ [(A_τ, ι_τ)] (43.6.15) is a bijection."
  (Proved on pp. 819–823; Lemma 43.6.16 makes `E_τ` a Riemann form after fixing the sign of `μ`.)
* Proposition 43.6.28, p. 822: "Every principally polarized complex abelian surface with QM by (O, μ) is isomorphic
  as such to one of the form (A_τ, ι_τ) for some τ ∈ H²." (Proved; the proof shows `Λ = ι_∞(O)x`.)

Pages are those of the Springer print, from a reading of the Springer PDF; the readings of this row used the
author's PDF, where these items sit 14 pages earlier (Theorem 43.4.6 p. 796; the setting spans pp. 803–804, with
`O` maximal and `μ² + D = 0` on p. 804; 43.6.12 and 43.6.14 p. 805; Proposition 43.6.28 p. 808; 43.7.1 p. 810).
The proof of Proposition 43.6.28 obtains `Im τ > 0` "By Lemma 43.4.17", which only normalizes a period matrix, not
the `O`-generator `x`; a unit of norm `−1` repairs it (43.7.1; Example 28.6.5). The printed statement, which is what
this leaf cites, is unaffected.

*Lean form.* Three clauses over the kernel's objects:
1. (43.6.12 with 43.6.14: the map is defined) every `τ ∈ ℍ` is the period of a complex abelian surface with
   `𝒪`-action, `(A, ι) ≅ (A_τ, ι_τ)` (`IsQMTorusAt`); that `A_τ` is an abelian surface uses Lemma 43.6.16's Riemann
   form `E_τ` with Lemma 43.6.22 (principal) and Lemma 43.6.23;
2. (Prop. 43.6.28: the map is onto) every complex abelian surface `A` with an injective ring map `ι : 𝒪 → End(A)`
   (`QMStr A`) carrying a principal polarization of type `μ` (`HasPrincipalRiemannMu`) has `(A, ι) ≅ (A_τ, ι_τ)`
   for some `τ ∈ ℍ`;
3. (43.6.14: the map is injective) two presentations of one `(A, ι)` have periods `τ, τ' ∈ ℍ` with `γ τ = τ'` for
   some `γ ∈ 𝒪`, `nrd γ = 1`, i.e. `τ' ∈ Γ τ` (the print writes `τ = γ τ'`; the Lean `γ` is the print's `γ⁻¹`).

*Identifications.* Voight's `B`, `O`, `ι_∞` are the kernel's `B = (2, −3 | ℚ)` (discriminant 6), the maximal order
`𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩` and `BPAnalytic.QM.iota`; `H² = ℍ`; Voight's `Γ = ι_∞(O¹)/{±1}` acts on `ℍ`
by Möbius transformations through `ι`. Voight's `μ` is `±` the kernel's `μ = 2j + ij` (`μ² = −6`): the
involution `x* = μ⁻¹ x̄ μ` (Voight (43.6.8)) is the same for both signs, and Lemma 43.6.16's sign fix picks `−μ`
(for the kernel's `μ`, `E_i(i v, v) < 0`). A "complex abelian surface" (Voight §43.4: a complex torus that carries a
Riemann form) is read as a kernel `PkgI3.AbVar ℂ` of dimension 2: in clause 1, `A_τ` algebraizes by Riemann's
criterion (Theorem 43.4.6, printed without proof and attributed to Riemann) and its holomorphic endomorphisms are
algebraic (Chow, GAGA; background), so `ι_τ` gives a `QMStr`; in clauses 2 and 3, algebraic endomorphisms act
analytically. "`(A, ι)` isomorphic to `(A_τ, ι_τ)`" is an `𝒪`-equivariant analytic isomorphism `ℂ²/Λ_τ ≅ A(ℂ)`
(`IsQMTorusAt`). In clause 3, `A.dim = 2` is forced by `IsQMTorusAt` (background).

*Dropped or changed clauses.* Clause 1 drops the polarization `E_τ` and its uniqueness (Lemmas 43.6.22–43.6.23;
over `ℂ` the kernel proves Lemma P on `H₁`, `Y3Hodge.lemmaP_H1`); clause 2 drops "as such" in the conclusion
(the isomorphism need not respect polarizations), which weakens it. The `Γ`-invariance direction of 43.6.14
(`(A_{γτ}, ι_{γτ}) ≅ (A_τ, ι_τ)`, (43.6.29)) is not a conjunct. Clause 3 drops "as such" in the hypothesis, which
strengthens it; it is still a consequence of the print: the printed injectivity proof (p. 823) uses only a
`φ ∈ GL₂(ℂ)` commuting with `ι_∞`, no polarization (alternatively, Lemma 43.6.23's uniqueness on `A_τ` applies);
on that route `nrd γ = +1` holds only because both periods lie in `H²` (the proof writes `H^{2±}`). -/
def VoightQMComplexModuliPrint : Prop :=
  (∀ τ : UpperHalfPlane, ∃ (A : PkgI3.AbVar ℂ) (_ : A.dim = 2) (q : QMStr A), IsQMTorusAt A q τ) ∧
  (∀ A : PkgI3.AbVar ℂ, A.dim = 2 → ∀ q : QMStr A, HasPrincipalRiemannMu A q →
    ∃ τ : UpperHalfPlane, IsQMTorusAt A q τ) ∧
  (∀ (A : PkgI3.AbVar ℂ) (q : QMStr A) (τ τ' : UpperHalfPlane), IsQMTorusAt A q τ → IsQMTorusAt A q τ' →
    ∃ γ : B, γ ∈ O ∧ ShimuraGlue.nrdQ ℚ γ = 1 ∧
      ∃ M : GL (Fin 2) ℝ, (M : Matrix (Fin 2) (Fin 2) ℝ) = BPAnalytic.QM.iota γ ∧ M • τ = τ')

/-! ## 3. T2b: Cornut–Vatsal, Doc. Math. 10 (2005), §3 (Shimura's canonical model at level `K₃`) -/

/-- **The complex points of a curve over `ℚ` uniformized at level `K₃`** (Cornut–Vatsal §3.1.1; Boutot–Carayol
III.0.1): `ψ : ℍ^± × G(𝔸_f) → M(ℂ)` is onto, its fibres are the classes of `G(ℚ) \ (G(𝔸_f)/K₃ × X)` (left action
of `G(ℚ) = B^×` on both factors, `K₃` on the right of `G(𝔸_f)`), and it is holomorphic in `z ∈ ℍ` for every `g`
(`M(ℂ)` is the Riemann surface `G(ℚ) \ (G(𝔸_f)/K₃ × X)`). -/
def UnifK3 (M : Over (Spec (CommRingCat.of ℚ))) (ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ M)) : Prop :=
  (∀ y : fieldPt ℂ ⟶ M, ∃ z g, ψ z g = y) ∧
  (∀ z g z' g', ψ z g = ψ z' g' ↔ DCRelPM z g z' g') ∧
  (∀ g, ShimuraSplit.IsHolFamily (X := M.left) (fun τ => (ψ (toPM τ) g).left))

/-- **CV Lemma 3.11 at level `K₃`, in Cornut–Vatsal's normalization**: for a CM point `z ∈ ℍ` of an embedding
`q : K → B` of an imaginary quadratic field and `σ = rec_K(λ)` on `K^ab`, `σ` acts on the CM points by left
multiplication by `λ^ε`: `σ ψ(z, g) = ψ(z, q̂(λ)^ε g)`. Cornut–Vatsal's `rec_K` sends uniformizers to geometric
Frobenius (§3.2.4), and the kernel's `ArtinCondC` is arithmetic: `ArtinCondC κ σ s` says `σ ∘ j = j ∘ art_K(s)` with
`art_K = TauCeti.ClassFieldTheory.ideleClassArtinMap`, which is `globalArtinMap` read in `Gal(L/K)`
(`TauCeti.ClassFieldTheory.of_ideleClassArtinMap`) and sends the prime idele class at an unramified place to
arithmetic Frobenius (`TauCeti.ClassFieldTheory.globalArtinMap_primeIdeleClass_eq_of_isArithFrobAt`). So
`σ = rec_K(λ)` is `ArtinCondC κ σ λ⁻¹`. The Boolean `δ` says whether `κ` or its conjugate is the eigencharacter of
`q(K)` on `(z, 1)ᵀ` (`IsCMPoint`); it is determined by `ε` and the identification of `X` with `ℍ^±`, and is left
existential. -/
def CVReciprocityAt (M : Over (Spec (CommRingCat.of ℚ))) (ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ M))
    (ε : ℤˣ) (δ : Bool) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
  ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] B) (z : UpperHalfPlane),
    IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
  ∀ (σ : ℂ ≃+* ℂ) (lam : IdeleGroup (𝓞 K) K), ArtinCondC κ σ lam⁻¹ →
  ∀ g : BAQˣ, galPt σ (ψ (toPM z) g) = ψ (toPM z) (qHatU q lam ^ (ε : ℤ) * g)

/-- **T2b (print-shaped): Shimura's canonical model at level `K₃`, its complex points, and the reciprocity law
at CM points.**

*Print.* C. Cornut, V. Vatsal, *CM points and quaternion algebras*, Documenta Math. 10 (2005) 263–309
(refereed: "Received: December 23, 2004 / Communicated by Peter Schneider", p. 263; open access).
* §3.1.1, p. 291: "Let S be a set of finite primes such that |S|+d is odd, and let B denote the quaternion algebra
  over F which ramifies precisely at S∪{τ₂, ⋯, τ_d} … Let G be the reductive group over ℚ whose set of points on a
  commutative ℚ-algebra A is given by G(A) = (B ⊗ A)^×." "Fix ε = ±1 and let X be the G(ℝ)-conjugacy class of the
  morphism from 𝕊 = Res_{ℂ/ℝ}(𝔾_{m,ℂ}) to G_ℝ which maps z = x + iy ∈ 𝕊(ℝ) = ℂ^× to [(x y; −y x)^ε, 1, ⋯, 1]".
  "For every compact open subgroup H of G(𝔸_f), the quotient of G(𝔸_f)/H × X by the diagonal left action of G(ℚ) is
  a Riemann surface M_H^an = G(ℚ)\(G(𝔸_f)/H × X) which is compact unless d = 1 (F = ℚ) and S = ∅ (G = GL₂). The
  Shimura curve M_H is Shimura's canonical model for M_H^an. It is a smooth curve over F (the reflex field) whose
  underlying Riemann surface M_H(ℂ) equals M_H^an."
* §3.2.1, Lemma 3.7, p. 296: "The map g ↦ [1, h] · g = [g, h] induces a bijection T(ℚ)‾\G(𝔸_f) ⥲ CM where T(ℚ)‾
  is the closure of T(ℚ) in T(𝔸_f)."
* §3.2.4, p. 298: "(1) reciprocity maps send uniformizers to geometric Frobenius; (2) Galois actions on geometric
  points are left actions." (§3.2.4 says it follows [14] instead of [4].)
* Lemma 3.11, p. 299: "The CM points are algebraic, defined over the maximal abelian extension K^ab of K. For
  σ = rec_K(λ) with λ ∈ T(𝔸_f) = K̂^×, the action of σ on CM ≃ T(ℚ)‾\G(𝔸_f) is given by multiplication on the left
  by λ^ε." (Introduced on p. 299 by "We thus obtain:", after a norm computation.)

*Lean form.* Some smooth curve `M` over `ℚ` with `ψ : ℍ^± × (B ⊗ 𝔸_f)^× → M(ℂ)` satisfies `UnifK3`
(§3.1.1 at `H = K₃`) and `CVReciprocityAt` for some `ε`, `δ` (Lemmas 3.7 and 3.11 at `H = K₃`).

*Identifications.* `F = ℚ`, `d = 1`, `S = {2, 3}`: Cornut–Vatsal's `B` is the quaternion algebra over `ℚ` ramified
exactly at `2, 3`, i.e. the kernel's `(2, −3 | ℚ)`; `G(𝔸_f) = (B ⊗ 𝔸_f)^×` (`BAQˣ`), `H = K₃` (`K3Q`). `X` is
identified with `ℍ^± = ℂ ∖ ℝ` (`HPM`), `GL₂(ℝ)` acting by Möbius transformations through `ι`: for `ε = 1` by
Cornut–Vatsal's Remark 3.15 (p. 301), the holomorphic `G(ℝ)`-equivariant map `g h₁ g⁻¹ ↦ g · i`; for `ε = −1` by
`g h₋₁ g⁻¹ ↦ g · (−i)` (not printed). The point `[g, h_z]` is written `ψ(z, g)`. A CM point of `(K, q)` (`h` factoring
through `T_ℝ`, `T = Res_{K/ℚ} 𝔾_m` embedded by `q`) lying in `ℍ` is a `z` with `IsCMPoint q κ z` for the
eigencharacter `κ`. `λ ∈ K̂^×` is the finite part of an idele (the archimedean component acts trivially, `K` being
imaginary quadratic), and `rec_K(λ) = art_K(λ)⁻¹` (see `CVReciprocityAt`). Level `K₃`: Cornut–Vatsal state the
level-`H` forms themselves (`CM/H ≃ CM_H` and `T(ℚ)\G(𝔸_f)/H ≃ CM_H`, §3.2 and §3.2.5, p. 300; used at level `H` in
§3.3.1, p. 302).

*Dropped clauses* (weaker): the particular `ε` and the resulting `δ` (both existential); CM points in `ℍ⁻`;
"compact"; Lemma 3.7's bijectivity (only its parametrization `g ↦ [g, h]` is used); the field of definition `K^ab`;
all levels other than `K₃`. -/
def CornutVatsalCMReciprocityPrint : Prop :=
  ∃ (M : Over (Spec (CommRingCat.of ℚ))) (ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ M)),
    SmoothOfRelativeDimension 1 M.hom ∧ UnifK3 M ψ ∧ ∃ (ε : ℤˣ) (δ : Bool), CVReciprocityAt M ψ ε δ

/-! ## 4. W-a (GLUE): the fine moduli scheme at `K₃` is Shimura's canonical model -/

/-- **W-a (GLUE, not a print; the one comparison the printed statements above do not make).**

For every smooth curve `M` over `ℚ` with a uniformization `ψ` having the properties of T2b, and every witness
`(Y, Φ)` of the polarization-free fine moduli problem at full level 3 (`Y3Fix.R1fpPropsAbP`), there is an
isomorphism `f : Y ≅ M` over `ℚ` carrying the moduli point of `[z, g]` to `ψ(z, g)`: if `P` is the moduli object of
`[z, g]` (`IsLevelPoint`), then `ψ(z, g) = f(Φ⁻¹[P])`.

*Status.* No legally readable refereed print read for this row states it. It combines (i) the identification of the
fine moduli `ℚ`-scheme of QM abelian surfaces with full level-3 structure, with its complex moduli description, with
Shimura's canonical model (Shimura, Ann. of Math. 85 (1967), Main Theorem I; Deligne's PEL route, Sém. Bourbaki 389,
4.11–4.21 and 5.7–5.8), and (ii) a uniqueness of canonical models applied at level `K₃` alone. Cornut–Vatsal
characterize `M_H` as a model of the whole Riemann surface, through the reciprocity law of the whole system
(§3.1.2, p. 292: "Among the models of M_H^an, the Shimura curve M_H is characterized by specifying the action of
Galois (the "reciprocity law") on certain special points"; Deligne 5.5); applying that characterization to every
`(M, ψ)` with T2b's clauses at `K₃` only is part of this GLUE. Boutot–Carayol state both structures on `S_U`
(III.0.1, p. 125: "Sa ℚ-structure a été définie par Shimura"; 1.4, p. 129: the moduli problem "est en fait défini et
représentable sur le corps ℚ, et l'on peut le prendre comme définition de la ℚ-structure sur S_U") but never compare
them. -/
def FineModuliCanonicalModelGlue : Prop :=
  ∀ (M : Over (Spec (CommRingCat.of ℚ))) (ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ M)),
    SmoothOfRelativeDimension 1 M.hom → UnifK3 M ψ → (∃ (ε : ℤˣ) (δ : Bool), CVReciprocityAt M ψ ε δ) →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), Y3Fix.R1fpPropsAbP Y Φ →
      ∃ f : Y ≅ M, ∀ (z : HPM) (g : BAQˣ) (P : QML3 ℂ), IsLevelPoint P z g →
        ψ z g = (Φ ℂ).symm (M3.mk P) ≫ f.hom

/-! ## 5. T2c: Boutot–Carayol, Astérisque 196–197, Ch. III §§0–1 -/

/-- **T2c (print-shaped): the moduli scheme of the polarization-free problem at level `U(3) = K₃`, and its complex
points.**

*Print.* J.-F. Boutot, H. Carayol, *Uniformisation p-adique des courbes de Shimura : les théorèmes de Čerednik et
de Drinfeld*, Astérisque 196–197 (1991) 45–158, Ch. III. Notation: `Δ` the indefinite quaternion division algebra
over `ℚ`, `𝒪_Δ` a maximal order, `W = 𝒪_Δ` as a left module, `U ⊂ Δ*(𝔸_f)` compact open.
* III.0.1, p. 125: "On associe alors à ces données la courbe de Shimura, notée S_U, définie sur ℚ, dont l'ensemble
  des points complexes est décrit par la formule suivante : S_U(ℂ) = Δ*(ℚ)\[𝓗^± × Δ*(𝔸_f)/U]." "C'est en
  particulier une surface de Riemann compacte, mais en général disconnexe."
* Théorème (1.1), p. 128: "La courbe S_U/ℂ représente, si U est assez petit (voir plus loin), le foncteur
  𝓜_U : Sch/ℂ → 𝓔ns défini comme suit : Pour S ∈ Sch/ℂ, 𝓜_U(S) est l'ensemble des classes d'isomorphie de triplets
  (A, ι, ν̄) tels que : (i) A est un schéma abélien sur S de dimension relative 2. (ii) ι : 𝒪_Δ → End_S A est une
  action de 𝒪_Δ sur A. (iii) ν̄ est une structure de niveau U sur A."
* 1.2(a), p. 128: "Dans le cas particulier où U = U(N) est le sous-groupe des unités de (𝒪_Δ ⊗ Ẑ) qui sont congrues
  à 1 modulo un entier N, une structure de niveau U (ou N) est la donnée d'un isomorphisme 𝒪_Δ-linéaire :
  ν : A_N ≃ W ⊗ (ℤ/Nℤ)."
* 1.3, p. 129: "Il suffit par exemple (voir [Bo]) que U soit contenu dans U(M) pour M un entier ≥ 3."
* 1.4, p. 129: "Le problème de modules que nous venons de décrire est en fait défini et représentable sur le corps
  ℚ, et l'on peut le prendre comme définition de la ℚ-structure sur S_U. Dans [Mi] et [Bo], on explique comment il se
  prolonge et définit un schéma en courbes propre et lisse au-dessus de ℤ[1/δN], où N est un entier tel que
  U(N) ⊂ U."

*Provenance.* III.0.1 (citing [De] for the ℚ-structure), Theorem 1.1 (citing [Mi], [Gi]), 1.2 and 1.3 (citing [Bo])
and the second sentence of 1.4 (citing [Mi], [Bo]) are stated in the print, not proved there; the first sentence of
1.4 carries no citation. Only Proposition 1.5 is proved in the print (`BoutotCarayolPolarizationPrint`). Refereeing: the volume's
Introduction (p. 1) says it "est issu d'un Séminaire" and that its first three articles, this one included, come from
the seminar's talks; whether the article counts as published is the maintainer's ruling.

*Lean form.* Some `(S, Φ_S)` satisfies the kernel's printed fine-moduli clause list `Y3Fix.R1fpPropsAbP` (1.1–1.4 at
`U = U(3)`, read over `ℚ`): properness and smoothness of relative dimension 1 over `ℚ` are the generic fibre of the
proper smooth curve over `ℤ[1/δN]` of 1.4's second sentence; the moduli bijections on field points, natural in the
field, the universal object and the classifying maps of families over proper smooth `ℚ`-curves are the
representability of 1.4's first sentence, read on field points (the kernel's `IsFibreOf` does not ask for
compatibility with the group laws, which rigidity supplies; background). And `S(ℂ)` is uniformized by
`B^× \ (ℍ^± × (B ⊗ 𝔸_f)^× / K₃)` holomorphically (`UnifK3`): `S ⊗ ℂ` and Boutot–Carayol's `S_U/ℂ` both represent
`𝓜_U` over `ℂ` (Theorem 1.1), so they are isomorphic (Yoneda), and III.0.1 gives the complex points; holomorphy is
the complex structure of the "surface de Riemann" (background, GAGA).

*Identifications.* `Δ = (2, −3 | ℚ)`, `δ = 6`, `𝒪_Δ = 𝒪`, `U = U(3) = K₃` (`K3Q`), `𝓗^± = ℂ ∖ ℝ` (`HPM`),
`Δ*(𝔸_f) = BAQˣ`. Boutot–Carayol's standing hypotheses hold: §0.2 asks `U = U_p^n · U^p` at the primes `p | δ`, and
`U(3)` has this form at `p = 2` with `n = 0`; §0.5 asks a maximal order stable under the canonical involution,
which `𝒪` is. Their "action" `ι` is a unital ring map; injectivity (the kernel's `QMStr`) is automatic in
characteristic 0 (background). A level structure `ν : A_3 ≃ W ⊗ ℤ/3ℤ` is the kernel's `LevelPrint` with `η = ν⁻¹`
(over `ℚ`-schemes by the finite étale argument, 3 being invertible; over fields by counting the 81 points;
background, neither printed nor proved in Lean). The bijection of III.0.1 itself is not specified in the print and
is existential here.

*Dropped clauses* (weaker): representability is read only through `R1fpPropsAbP` (universal property for families
over proper smooth `ℚ`-curves, on field points); the integral model over `ℤ[1/δN]` itself (only its generic fibre
is used); all levels other than `U(3)`. -/
def BoutotCarayolModuliPrint : Prop :=
  ∃ (S : Over (Spec (CommRingCat.of ℚ))) (ΦS : PtEquiv S), Y3Fix.R1fpPropsAbP S ΦS ∧
    ∃ ψS : HPM → BAQˣ → (fieldPt ℂ ⟶ S), UnifK3 S ψS


/-- **T2c′ (print-shaped): the principal *-polarization of a complex QM surface.**

*Print.* Boutot–Carayol, loc. cit., 1.5 and Proposition (1.5), p. 129: "une *-polarisation est une polarisation λ de
A telle que, en chaque point géométrique s de S, l'involution de Rosati correspondante sur End⁰(A_s) induise sur 𝒪_Δ
(via ι) l'involution *." "PROPOSITION (1.5). — Soit S un schéma de caractéristique 0 et (A, ι, ν̄) ∈ 𝓜_U(S). Alors il
existe sur A une *-polarisation principale. Une telle polarisation est unique." Here `x* = t⁻¹ x̄ t` for one fixed
`t ∈ 𝒪_Δ` with `t² = −δ` (III.0.5, p. 127). Over `ℂ` the same statement is Voight's Remark 43.6.27 (Springer p. 821,
author's PDF p. 808), whose printed justification covers `A_τ` only.

*Provenance.* The existence of a *-polarization, unique up to a rational number, is cited ([Mi] Lemma 1.1 or [Bo]
§8); the reduction to `S = Spec(ℂ)` is asserted; principality is proved through Lemme (1.6) and Sous-lemme (1.7),
p. 130, in sketch ("clairement", "vérifié immédiatement"). Refereeing: as for `BoutotCarayolModuliPrint` (a
seminar volume; the maintainer's ruling).

*Lean form.* Every complex QM surface with full level-3 structure (`P : QML3 ℂ`, an object of `𝓜_{U(3)}(Spec ℂ)`)
has a principal Riemann form of type `μ` (`HasPrincipalRiemannMu`).

*Identifications.* `S = Spec ℂ`, `δ = 6`; `t = μ = 2j + ij ∈ 𝒪` (coordinates `(−2, −1, 4, 2)` in the basis
`1, i, (1+j)/2, (i+k)/2`), `μ² = −6 = −δ`, so `*` is the kernel's `Y3Hodge.dagO`. The proof of (1.5) uses only that
`t ∈ GL₂(ℤ_ℓ)` for `ℓ ∤ δ` and that `t` is a uniformizer at `ℓ | δ` (Sous-lemme 1.7 and the Remarque, p. 130); `μ`
satisfies both, `nrd μ = 6`, and the sign of `t` does not change `*`. A polarization of `A/ℂ` is read as a Riemann
form on a uniformization through the Appell–Humbert theorem (Mumford, *Abelian varieties*, §§2–3; background),
principal as unimodular. The level structure is in the hypothesis (`P : QML3 ℂ`) and plays no role in the conclusion.

*Dropped clauses* (weaker): uniqueness; bases other than `Spec ℂ`. -/
def BoutotCarayolPolarizationPrint : Prop :=
  ∀ P : QML3 ℂ, HasPrincipalRiemannMu P.A P.q

end DelignePS
