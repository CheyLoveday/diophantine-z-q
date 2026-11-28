import ZInQKernel.Contrib.OneProof.DelignePrintShaped.Assembly

/-! # The row `deligneCanonicalModelY3EveryPrint` from Milne's existence argument: print-shaped statements

A second reduction of `Y3Hodge.DeligneCanonicalModelY3EveryPrint`, with no comparison statement. The reciprocity law
comes from Milne's criterion for a model to be canonical (the PEL case of §14). Holomorphy comes from the family of
abelian surfaces over the complex Shimura curve (Milne, Theorem 14.8, as used in §14) together with the
representability of the moduli problem over `ℚ` (Boutot–Carayol 1.4). T2c″ and M2 are the print or weaker; M1 is a
consequence of printed statements, with the derived steps listed in its docstring:

* `MilneShimuraFamilyPrint` (M1): the complex Shimura curve at level `K₃`, uniformized holomorphically by
  `ℍ^± × (B ⊗ 𝔸_f)^×`, with a family of QM abelian surfaces with level-3 structure whose fibre over `[z, g]` is the
  moduli object of `[z, g]`;
* `BoutotCarayolRepresentabilityPrint` (T2c″): the moduli problem at `U(3) = K₃` is representable over `ℚ`, read on
  families over proper smooth curves over `ℚ` and over `ℂ`;
* `MilneCanonicalModelPrint` (M2): a model over `ℚ` on which `Aut(ℂ)` acts as on the moduli objects satisfies the
  reciprocity law (54) at the CM points.

The companion file proves the row from these, T2a (`DelignePS.VoightQMComplexModuliPrint`) and T2c′
(`DelignePS.BoutotCarayolPolarizationPrint`); the analytic representation of homomorphisms enters through the proved
`ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof`.

*Source of M1 and M2.* J. S. Milne, *Introduction to Shimura varieties*, in: *Harmonic analysis, the trace formula,
and Shimura varieties*, Clay Mathematics Proceedings 4, American Mathematical Society, 2005, pp. 265–378. Page numbers
are those of the volume. The project counts this volume as published.
-/

set_option autoImplicit false

noncomputable section

namespace DelignePSMilne

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open ShimuraCFT RayClassCFT
open Y3Hodge (HPM DCRelPM toPM)
open DelignePS

/-! ## 1. M1: the family of abelian surfaces over the complex Shimura curve -/

/-- **M1 (a consequence of printed statements): the complex Shimura curve at level `K₃` with its family of QM
abelian surfaces.**

*Print.* Milne, loc. cit.
* Theorem 3.12 (Baily and Borel 1966), pp. 291–292: "Let D(Γ) = Γ\D be the quotient of a hermitian symmetric domain
  by a torsion free arithmetic subgroup Γ of Hol(D)⁺. Then D(Γ) has a canonical realization as a zariski-open subset
  of a projective algebraic variety D(Γ)*. In particular, it has a canonical structure as an algebraic variety."
* Proposition 3.8, p. 290: "There is a unique functor (V, O_V) ↦ (V^an, O_{V^an}) from nonsingular varieties over C to
  complex manifolds with the following properties: (a) as sets, V = V^an, every zariski-open subset is open for the
  complex topology, and every regular function is holomorphic; …"
* Theorem 6.8 (Riemann's theorem), p. 319: "The functor A ↦ H₁(A, Z) is an equivalence from the category AV of
  abelian varieties over C to the category of polarizable integral hodge structures of type (−1, 0), (0, −1)."
* p. 352: "Let V be a nonsingular algebraic variety over C. A family of abelian varieties over V is a regular map
  f : A → V of nonsingular varieties plus a regular multiplication A ×_V A → A over V such that the fibres of f are
  abelian varieties of constant dimension (in a different language, A is an abelian scheme over V)." "Theorem 14.8.
  Let V be a nonsingular variety over C. There is an equivalence (A, f) ↦ (R¹f_*Z)^∨ from the category of families of
  abelian varieties over V to the category of polarizable integral variations of hodge structures of type (−1, 0),
  (0, −1) on S." (Sic: `S` for `V`.) "This is a generalization of Riemann's theorem (6.8) — see Deligne 1971a, 4.4.3."
  The cited statement: P. Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), p. 51: "Rappel (4.4.3). — Soit S
  un schéma lisse de type fini sur C. La construction (4.4.2) établit une équivalence de catégorie entre : a) la
  catégorie des schémas abéliens sur S; b) la catégorie des familles continues polarisables de structures de Hodge H de
  type (−1, 0)+(0, −1) sur S, telles que H_Z soit sans torsion et que la filtration de Hodge varie holomorphiquement
  sur S." (The scan prints the zeros as "o".) It continues: "la pleine fidélité résulte que ce que, pour X₁ et X₂ deux
  schémas abéliens sur S, le S-schéma Hom_S(X₁, X₂) est non ramifié sur S, donc a mêmes sections algébriques ou
  holomorphes." (Sic.)
* p. 354, in the outline of the existence of canonical models (Siegel case): "Then Sh^ε_K = Γε\X⁺ where
  Γε = G(Q) ∩ Kε for some conjugate Kε of K (see 5.17, 5.23)". "Write X⁺(Γε) for Γε\X⁺ regarded as an algebraic
  variety". "Fix a lattice Λ in V that is stable under the action of Γε. From the action of Γε on Λ, we get a local
  system of Z-modules M on X⁺(Γε) (see 14.7), which, in fact, is a polarized integral variation of hodge structures F.
  According to Theorem 14.8, this variation of hodge structures arises from a polarized family of abelian varieties
  f : A → X⁺(Γε)." For the case at hand (p. 354): "Simple PEL Shimura varieties of type A or C. The proof is similar
  to the Siegel case."

*Lean form.* There are a proper smooth curve `T` over `ℂ` (`Sh_{K₃}`, with the algebraic structure of Theorem 3.12 on
each component `Γε\X⁺`), a family `𝒜` over `T` of abelian surfaces with `𝒪`-action and printed level-3 structure
(`Y3Fix.QMAbSchemeP`), and `ψ : ℍ^± × (B ⊗ 𝔸_f)^× → T(ℂ)` (`ℂ`-points of `T` over `ℂ`), onto
(`T(ℂ) = Sh_{K₃}(ℂ)`) and holomorphic in `τ ∈ ℍ` for every `g` (Proposition 3.8: the complex structure of `Γε\X⁺`),
such that the fibre of `𝒜` at `ψ(z, g)` is a moduli object of `[z, g]` (`DelignePS.IsLevelPoint`).

*Status: a consequence of the printed statements above, not a direct instance of one of them.* The steps from the
print to the Lean form (to be read; not printed as such):
1. *Properness.* `Γε\ℍ` is compact because `B` is a division algebra, and `π₀(Sh_{K₃}) ≅ ℚ_{>0} \ 𝔸_f^× / ν(K₃)` is
   finite (5.17); so `T` is projective (Theorem 3.12, the compactification adding nothing).
2. *Smoothness at `K₃`.* `Γε` contains no torsion other than `1` (in particular not `−1`): for `γ = g k g⁻¹ ∈ Γε` with
   `k ∈ K₃`, `nrd(γ − 1) = nrd(k − 1) ∈ 9ℤ`, while a root of unity `γ ≠ 1` of `B` with `nrd γ = 1` has
   `nrd(γ − 1) = 2 − trd γ ∈ {1, 2, 3, 4}`. So `Γε` acts freely on `ℍ`, and `Γε\ℍ` is a compact Riemann surface.
3. *The PEL case.* Milne writes the construction of p. 354 for the Siegel case and states "The proof is similar" for
   PEL. On the component of `[z, g]` take `Λ = L_g = B ∩ 𝒪̂ g⁻¹` in `V = B`, stable under `Γε = B^× ∩ g K₃ g⁻¹`
   (acting by right multiplication by inverses); with the Hodge structures `h_x` it is a polarizable integral
   variation of Hodge structures of type `(−1, 0), (0, −1)` on each component (polarized by the Riemann form `ψ` of the
   PEL datum, §8). By Theorem 14.8 (Deligne's 4.4.3) it comes from a family whose fibre at the image of `x` has
   `H₁ = Λ` with the Hodge structure `h_x` (fibrewise Theorem 6.8), i.e. it is `ℂ² / ι(L_g)(z, 1)ᵀ`.
4. *The `𝒪`-action.* Left multiplication by `𝒪` on `Λ` commutes with `Γε` and with `h_x` (both act on the right), so it
   is an endomorphism of the variation of Hodge structures, hence of the family, by the full faithfulness in 4.4.3
   (Deligne's sentence above).
5. *The level-3 sections.* `Γε` acts trivially on `Λ/3Λ` (`y k⁻¹ g⁻¹ ≡ y g⁻¹ mod 3𝒪̂ g⁻¹` for `y ∈ 𝒪̂`, `k ∈ K₃`), so the
   local system `Λ/3Λ`, which is the `3`-torsion of the family, is constant, and `a ↦ a g⁻¹/3` gives `𝒪`-linear
   analytic sections, bijective onto the `3`-torsion of every fibre. They are algebraic by Chow's theorem
   (Theorem 3.11) on the finite étale `𝒜[3]`, which is projective over `T`; the printed level condition
   (`Y3Fix.LevelPrint`) then holds at every geometric point, non-closed ones included, by the finite étale
   comparison. For `g = u ∈ 𝒪̂^×` the sections are `η(a) = ℓ_τ(a w)/3` with `w ≡ u⁻¹ (mod 3)`, the convention of
   `DelignePS.IsLevelTorusAt`. A family of abelian varieties over a nonsingular complex variety in Milne's sense is an
   abelian scheme; with these structures it is a `Y3Fix.QMAbSchemeP` (the kernel's group-object and level clauses).
6. *The fibre clause.* The fibre at `ψ(z, g)` depends only on the point `[z, g]`, and `DelignePS.IsLevelPoint`
   describes the moduli object of `[z, g]` through a representative `(τ, u)` with `τ ∈ ℍ` and `u ∈ 𝒪̂^×`. That every
   `(z, g)` has one (strong approximation for `B¹` with Eichler's norm theorem, i.e. class number one) is proved in
   Lean: `DelignePS.exists_unit_rep`, from `Y3Hodge.exists_upper` and `RayClassCFT.classNumberOneB_proof`.

*Identifications.* `(G, X) = (B^×, ℍ^±)` with `B = (2, −3 | ℚ)`, a simple PEL datum of type C (Example 8.6,
Definition 8.15; `V = B` with `B` acting on the left, `G(ℚ) = B^×` acting by right multiplication by `γ⁻¹`, so that it
acts on `X = ℍ^±` by Möbius transformations through `ι` and on `G(𝔸_f) = (B ⊗ 𝔸_f)^×` by left multiplication), and
`K = K₃` (`K3Q`). The point `[z, g]` of `Sh_{K₃}(ℂ) = G(ℚ) \ X × G(𝔸_f) / K₃` is `ψ(z, g)`.

*Dropped clauses* (weaker): the polarization of the family; the fibres of `ψ` (only onto is kept); the
compactification and the uniqueness of the algebraic structure (Corollary 3.16); all levels other than `K₃`. -/
def MilneShimuraFamilyPrint : Prop :=
  ∃ (T : Over (Spec (CommRingCat.of ℂ))), IsProper T.hom ∧ SmoothOfRelativeDimension 1 T.hom ∧
    ∃ (𝒜 : Y3Fix.QMAbSchemeP T.left) (ψ : HPM → BAQˣ → (Spec (CommRingCat.of ℂ) ⟶ T.left)),
      (∀ (z : HPM) (g : BAQˣ), ψ z g ≫ T.hom = 𝟙 _) ∧
      (∀ s : Spec (CommRingCat.of ℂ) ⟶ T.left, s ≫ T.hom = 𝟙 _ → ∃ (z : HPM) (g : BAQˣ), ψ z g = s) ∧
      (∀ g : BAQˣ, ShimuraSplit.IsHolFamily (X := T.left) (fun τ => ψ (toPM τ) g)) ∧
      ∀ (z : HPM) (g : BAQˣ), ∃ P : QML3 ℂ, IsLevelPoint P z g ∧ IsFibreOf 𝒜.toQMFamily (ψ z g) P

/-! ## 2. T2c″: representability over `ℚ`, on families over proper smooth complex curves -/

/-- **T2c″ (print-shaped): the moduli problem at `U(3) = K₃` is representable over `ℚ`; read on families over
proper smooth curves over `ℚ` (the kernel's `Y3Fix.R1fpPropsAbP`) and over `ℂ`.**

*Print.* J.-F. Boutot, H. Carayol, *Uniformisation p-adique des courbes de Shimura : les théorèmes de Čerednik et de
Drinfeld*, Astérisque 196–197 (1991) 45–158, Ch. III (see `DelignePS.BoutotCarayolModuliPrint` for 0.1, 1.1–1.3).
* 1.4, p. 129: "Le problème de modules que nous venons de décrire est en fait défini et représentable sur le corps ℚ,
  et l'on peut le prendre comme définition de la ℚ-structure sur S_U. Dans [Mi] et [Bo], on explique comment il se
  prolonge et définit un schéma en courbes propre et lisse au-dessus de ℤ[1/δN], où N est un entier tel que
  U(N) ⊂ U." (Here `δ = 6` and `N = 3`.)
* The problem is that of Théorème (1.1), p. 128: "𝓜_U(S) est l'ensemble des classes d'isomorphie de triplets (A, ι, ν̄)
  tels que : (i) A est un schéma abélien sur S de dimension relative 2. (ii) ι : 𝒪_Δ → End_S A est une action de 𝒪_Δ
  sur A. (iii) ν̄ est une structure de niveau U sur A.", at `U = U(3)` (1.2(a), 1.3).

*Lean form.* Some `(S, Φ_S)` satisfies `Y3Fix.R1fpPropsAbP` (as in `DelignePS.BoutotCarayolModuliPrint`: 1.1–1.4 at
`U(3)`, read over `ℚ`), and for every proper smooth curve `T` over `ℂ`, regarded as a `ℚ`-scheme through `ℚ → ℂ`, and
every family `𝒜` over `T` (`Y3Fix.QMAbSchemeP`) whose fibres at the `ℂ`-points of `T` over `ℂ` are objects, there is a
morphism `F : T → S` over `ℚ` (the classifying map of representability) such that the class of the fibre of `𝒜` at a
`ℂ`-point `s` is `Φ_S(F ∘ s)` (the pull-back of the universal object along `F ∘ s` is the fibre at `s`). Properness and
smoothness of relative dimension 1 of `S` over `ℚ` are the generic fibre of 1.4's second sentence. "Représentable sur
le corps ℚ" is read on all `ℚ`-schemes: the classifying maps for families over proper smooth curves over `ℚ`
(`Y3Fix.R1univAbPropsP`) and over `ℂ` (regarded as `ℚ`-schemes) are special cases.

*Identifications.* As in `DelignePS.BoutotCarayolModuliPrint`; in particular `K₃ = U(3)`, the units of `𝒪 ⊗ Ẑ`
congruent to 1 modulo 3 (1.2(a)), which is "assez petit" by 1.3, p. 129: "Il suffit par exemple (voir [Bo]) que U soit
contenu dans U(M) pour M un entier ≥ 3." A level structure `ν : A_3 ≃ W ⊗ ℤ/3ℤ` (1.2(a)) is read with `W ⊗ ℤ/3ℤ` the
constant group scheme. A `ℂ`-point of `T` over `ℂ` is a `ℂ`-point of `T` over
`ℚ`. A `Y3Fix.QMAbSchemeP` (an abelian scheme of relative dimension 2 with a unital ring action of `𝒪` and printed
level-3 structure) is an object of `𝓜_{U(3)}(T)`, and the fibre clause of the hypothesis holds for every such object
(background, as for the same clause in `Y3Fix.R1univAbPropsP`).

*Dropped clauses* (weaker): representability is read only on families over proper smooth curves over `ℚ` and over `ℂ`,
on field points, respectively `ℂ`-points; the uniqueness of the classifying map; the integral model of 1.4's second
sentence (only its generic fibre is used); all levels other than `U(3)`. *Provenance and refereeing:* the first
sentence of 1.4 carries no citation; the volume is a seminar volume (see `DelignePS.BoutotCarayolModuliPrint`), which
the project counts as published. -/
def BoutotCarayolRepresentabilityPrint : Prop :=
  ∃ (S : Over (Spec (CommRingCat.of ℚ))) (ΦS : PtEquiv S), Y3Fix.R1fpPropsAbP S ΦS ∧
    ∀ (T : Over (Spec (CommRingCat.of ℂ))), IsProper T.hom → SmoothOfRelativeDimension 1 T.hom →
    ∀ 𝒜 : Y3Fix.QMAbSchemeP T.left,
      (∀ s : Spec (CommRingCat.of ℂ) ⟶ T.left, s ≫ T.hom = 𝟙 _ →
        ∃ P : QML3 ℂ, IsFibreOf 𝒜.toQMFamily s P) →
      ∃ F : T.left ⟶ S.left, F ≫ S.hom = T.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)) ∧
        ∀ s : Spec (CommRingCat.of ℂ) ⟶ T.left, s ≫ T.hom = 𝟙 _ →
        ∀ y : fieldPt ℂ ⟶ S, y.left = s ≫ F →
        ∀ P : QML3 ℂ, IsFibreOf 𝒜.toQMFamily s P → ΦS ℂ y = M3.mk P

/-! ## 3. M2: Milne's criterion for a model to be canonical, PEL case -/

/-- **M2 (print-shaped): a model over `ℚ` on which `Aut(ℂ)` acts as on the moduli objects satisfies the reciprocity
law at the CM points.**

*Print.* Milne, loc. cit.
* §14, pp. 354–355: "Simple PEL Shimura varieties of type A or C. The proof is similar to the Siegel case. Here
  ShK(G, X) classifies quadruples (A, i, s, ηK) satisfying certain conditions. One checks that if σ fixes the reflex
  field E(G, X), then σ(A, i, s, ηK) lies in the family again (see 12.7). Again the special points correspond to CM
  abelian varieties, and the Shimura-Taniyama theorem shows that, if ShK(G, X) has a model MK over E(G, X) for which
  the action of Aut(C/E(G, X)) on MK(C) = ShK(G, X)(C) agrees with its action on the quadruples, then it is
  canonical." The Siegel case is Proposition 14.12, p. 353: "Suppose that ShK has a model MK over Q for which the map
  ℳK → MK(C) commutes with the actions of Aut(C). Then MK is canonical." (proved there in sketch, from the main
  theorem of complex multiplication), with the action on triples defined on p. 353: "We define σ(A, s, ηK) to be
  (σA, ^σs, ^σηK) with ^ση as in (55)" ((55), p. 347: `V(𝔸_f) → V_f(A) → V_f(σA)`, `σ` acting on torsion points).
* p. 343: "A model of V over k (or a k-structure on V) is a variety V₀ over k together with an isomorphism
  ϕ : V₀Ω → V."
* Definition 12.8, p. 346: "A model MK(G, X) of ShK(G, X) over E(G, X) is canonical if, for every special pair
  (T, x) ⊂ (G, X) and a ∈ G(Af), [x, a]K has coordinates in E(x)^ab and (54) σ[x, a]K = [x, rx(s)a]K, for all
  σ ∈ Gal(E(x)^ab/E(x)), s ∈ A×_E(x) with artE(x)(s) = σ."
* (51), p. 341: "artE(α) = recE(α)⁻¹", where (p. 340, (b)) recE sends "the idèle α = (1, . . . , 1, π, 1, . . .)" (`π`
  in the place `v`), "π a prime element of O_{E_v}", to "the Frobenius element (v, L/E)", the automorphism "acting as
  x ↦ x^(O_E : 𝔭_v) on O_L/𝔓".
* Definition 12.5, p. 345 (special pairs); (52)–(53), p. 345 (`r_x`); Example 12.4(c), p. 344: "If (G, X) is a simple
  PEL datum of type (A) or (C), then E(G, X) is the field generated over Q by {TrX(b) | b ∈ B} (Deligne 1971c, 6.1)."

*Status.* The PEL paragraph is itself an outline ("The proof is similar to the Siegel case"), and Proposition 14.12 is
proved in sketch. The steps below that connect the print to the Lean form are stated, not proved in Lean, unless a Lean
name is given.

*Lean form.* For every proper smooth curve `M` over `ℚ` with `ψ : ℍ^± × (B ⊗ 𝔸_f)^× → M(ℂ)` satisfying
`DelignePS.UnifK3` (a model of `Sh_{K₃}` over `E(G, X) = ℚ`): if `Aut(ℂ)` acts on the points `ψ(z, g)` as on the moduli
objects (`σ ψ(z, g) = ψ(z', g')` whenever the base change along `σ` of a moduli object of `[z, g]` is a moduli object
of `[z', g']`), then the reciprocity law (54) holds at the CM points of `ℍ`, in the form
`DelignePS.CVReciprocityAt` for some `ε`, `δ`.

*Identifications.*
* Model: `ψ` is holomorphic in `τ ∈ ℍ` (`ShimuraSplit.IsHolFamily`: regular functions on affine opens pull back to
  holomorphic functions, so `ψ(·, g)` is a holomorphic map into the complex manifold `M(ℂ)`); on `ℍ⁻` it is determined
  through `DelignePS.DCRelPM` by `γ = i` (`nrd i = −2 < 0`: `ψ(z, g) = ψ(i z, i g)`, `i z ∈ ℍ` for `z ∈ ℍ⁻`). Each
  `Γε` is torsion-free and cocompact (see `MilneShimuraFamilyPrint`, steps 1–2), so `ψ` induces a holomorphic bijection
  `Sh_{K₃}(ℂ) → M(ℂ)` of compact Riemann surfaces. A holomorphic bijection of Riemann surfaces is biholomorphic, hence
  (Chow, Theorem 3.11; Corollary 3.16) an isomorphism `Sh_{K₃} ≅ M ⊗ ℂ` of algebraic curves, the inverse of a model's
  `ϕ`. `E(G, X) = ℚ` by Example 12.4(c): `Tr_X(b)` is the trace of `ι(b)` on `ℂ²` (Remark 8.18(b)), i.e. the reduced
  trace of `b`, which is rational (`DelignePSMilne.Datum.exists_rat_trace_iota`).
* Quadruples: the quadruple of `[z, g]` (Theorem 8.17, with (**) automatic by Proposition 8.19, and `ker¹(ℚ, B^×) = 1`)
  and the kernel's moduli objects `P` of `[z, g]` (`DelignePS.IsLevelPoint`) correspond by
  `P ↦ (P.A, ι ⊗ ℚ, s_P, η̂ K₃)`: `s_P` the Riemann form of the principal `*`-polarization (unique: Boutot–Carayol 1.5);
  `η̂ : V(𝔸_f) → V_f(P.A)` an `𝒪̂`-linear isomorphism with `η̂(𝒪̂) = T̂(P.A)` reducing mod 3 to the level structure
  (`T̂(P.A)` is free of rank one over `𝒪̂`, and every level structure lifts because `(𝒪 ⊗ ℤ₃)^×` maps onto
  `(𝒪/3𝒪)^×`); the `K₃`-orbits of such `η̂` are exactly these pairs `(T̂, η̂ mod 3)`, and isomorphisms of objects are
  isomorphisms of quadruples. That every point `[z, g]` has a moduli object (non-vacuity, through strong approximation)
  is proved in Lean (`DelignePS.exists_unit_rep`, `DelignePS.exists_levelPoint`). Milne's `σ` on quadruples is then
  base change along `σ` (`σA`, `σi`; `^σs = s_{σP}` by uniqueness; `^ση` through torsion points, (55)), i.e. the
  kernel's `IsBaseChangeOf σ`, which does not ask compatibility with the group laws: rigidity supplies it (used in Lean
  in `DelignePSMilne.mk_eq_of_isBaseChangeOf`). The action of `σ` on `M(ℂ)` is `galPt σ` (`M` is over `ℚ`).
* Special pairs at `z ∈ ℍ`: `(T_q, h_z)` with `T_q = q(K)^×` for an embedding `q : K → B` of an imaginary quadratic
  field and `z` its CM point (`IsCMPoint q κ z`, `κ` the eigencharacter of `q(K)` on `(z, 1)ᵀ`); every special `z` is of
  this form. `σ = art_{E(x)}(s)` is the kernel's `ArtinCondC κ σ s⁻¹` (Tau Ceti's `art_K` sends prime idele classes to
  arithmetic Frobenius; see `DelignePS.CVReciprocityAt`), and `r_x(s) ∈ T_q(𝔸_f) = K̂^×` acts on `[z, g]` through
  `q̂`. For the reader (the statement does not depend on it): with `G(ℚ) = B^×` acting on `V = B` by right
  multiplication by `γ⁻¹` and `h_z(i)` the right multiplication by `J_z`, `μ_x(w)` is `(w⁻¹, 1)` in the coordinates
  `(κ, κ̄)` of `T_{q,ℂ}`, so `E(x) = κ(K)` and (52) gives `r_x(s) = s⁻¹`, i.e. `(ε, δ) = (−1, true)`.

*Dropped clauses* (weaker): "[x, a]K has coordinates in E(x)^ab"; special points in `ℍ⁻`; the particular `(ε, δ)`;
models at levels other than `K₃` and of the whole system (Definition 12.10). The hypothesis on the action is asked only
at the moduli objects of points `[z, g]` (every object is one, by T2a and T2c′). -/
def MilneCanonicalModelPrint : Prop :=
  ∀ (M : Over (Spec (CommRingCat.of ℚ))) (ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ M)),
    IsProper M.hom → SmoothOfRelativeDimension 1 M.hom → UnifK3 M ψ →
    (∀ (σ : ℂ ≃+* ℂ) (z : HPM) (g : BAQˣ) (z' : HPM) (g' : BAQˣ) (P Q : QML3 ℂ),
      IsLevelPoint P z g → IsLevelPoint Q z' g' → IsBaseChangeOf (σ : ℂ →+* ℂ) P Q →
      galPt σ (ψ z g) = ψ z' g') →
    ∃ (ε : ℤˣ) (δ : Bool), CVReciprocityAt M ψ ε δ

end DelignePSMilne
