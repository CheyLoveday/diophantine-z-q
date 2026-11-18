import ZInQKernel.Contrib.OneProof.RC.Height.Isomorphism
import ZInQKernel.Contrib.OneProof.RC.Height.BaseChange

/-!
# Lane RC19 (height): the sum/difference isogenies, their adjunction and the regulator ratio

The 11/5 manuscript (`diophantine_zq.tex`), proof of Proposition `ex:arith-central-calibration`,
lines 4020–4025 and 4082–4091:

> For restriction of scalars and the product of the two twists, the sum/difference isogenies are
> dual and compose to `[2]`. Their free-lattice indices satisfy `IJ = 2`, with regulator ratio
> `2/I²`. […] `I = [B(ℚ)_free : φ A(ℚ)_free]`, `J = [A(ℚ)_free : ψ B(ℚ)_free]`. Then `IJ = 2` and
> `Reg_B / Reg_A = 2/I²`.

Here `A = Res_{K/ℚ}(E^{(h)}_K)` and `B = E^{(h)} × E^{(hk)}`, `K = ℚ(√k)`.

**Form (DEPARTURE, recorded in the report).** Abelian surfaces, Weil restriction and dual abelian
varieties are not available in Lean, so `A` and `B` are represented by their groups of rational
points with their canonical height pairings: `A(ℚ) = E^{(h)}(K)` with the Néron–Tate pairing of
`E^{(h)}` relative to `K` (the vendored pairing over the number field `K`), and
`B(ℚ) = E^{(h)}(ℚ) × E^{(hk)}(ℚ)` with the sum of the two Néron–Tate pairings over `ℚ`. That these
are the canonical height pairings of `A` and `B` attached to the principal polarizations (the
trace polarization of the Weil restriction and the product polarization) is GLUE (it is what the
regulators in Milne's isogeny formula mean, tex 4024–4027). The isogenies are the explicit maps
on points:

* `ψ = sumMap : B(ℚ) → A(ℚ)`, `(Q, R) ↦ Q_K + ι(R_K)`, with `ι : E^{(hk)}_K ≃ E^{(h)}_K` the twist
  isomorphism (`Isomorphism.lean`);
* `φ = diffMap : A(ℚ) → B(ℚ)`, `P ↦ (P + σP, ι⁻¹(P − σP))`, both components descended to `ℚ`
  (`exists_baseChange_eq_of_map_eq`), `σ` the nontrivial automorphism of `K`.

Every declaration in this file is PROVED.

* `sumMap_diffMap`, `diffMap_sumMap`: `ψ ∘ φ = [2]` and `φ ∘ ψ = [2]` (tex 4022–4023).
* `pairingB_diffMap`: **the adjunction** `⟨φ P, x⟩_B = ⟨P, ψ x⟩_A` ("the sum/difference isogenies
  are dual"), from base change of heights (`[K : ℚ] = 2`), Galois invariance and the invariance of
  heights under the twist isomorphism.
* `heightB_diffMap`, `heightA_sumMap`: `ĥ_B(φ P) = 2 ĥ_A(P)` and `ĥ_A(ψ x) = 2 ĥ_B(x)`.
* `regulator_ratio_sumDiff`: with rank-one free generators `g_A`, `g_B` (rank one is an input:
  the forward theorems at known simple zeros, tex 4020–4021), there are `α, β ∈ ℤ` with
  `φ g_A ≡ α g_B`, `ψ g_B ≡ β g_A` modulo torsion, `αβ = 2` (so `IJ = 2` for `I = |α|`, `J = |β|`)
  and `Reg_B α² = 2 Reg_A`, i.e. `Reg_B / Reg_A = 2/I²` (tex 4082–4086).
-/

open Height

namespace ZInQ.Manuscript.RC.Height

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Contrib.CloudB3RC53

/-! ### Torsion bookkeeping in abelian groups -/

section Torsion

variable {G : Type*} [AddCommGroup G]

/-- A difference of torsion elements is torsion. PROVED. -/
theorem isOfFinAddOrder_sub' {x y : G} (hx : IsOfFinAddOrder x) (hy : IsOfFinAddOrder y) :
    IsOfFinAddOrder (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

/-- If `n • g` is torsion and `g` is not, then `n = 0`. PROVED. -/
theorem eq_zero_of_isOfFinAddOrder_zsmul {g : G} (hg : ¬IsOfFinAddOrder g) {n : ℤ}
    (h : IsOfFinAddOrder (n • g)) : n = 0 := by
  by_contra hn
  obtain ⟨m, hm, hmg⟩ := isOfFinAddOrder_iff_zsmul_eq_zero.mp h
  exact hg (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨m * n, mul_ne_zero hm hn, by
    rw [← smul_smul, hmg]⟩)

/-- **A free generator of a rank-one group**: `g` is not torsion and every element is an integer
multiple of `g` modulo torsion (`G/G_tors = ℤ g`). -/
def IsFreeGenerator (g : G) : Prop :=
  ¬IsOfFinAddOrder g ∧ ∀ P : G, ∃ n : ℤ, IsOfFinAddOrder (P - n • g)

end Torsion

/-! ### The quadratic field -/

/-- **The quadratic field `K = ℚ(√k)`**: an element `s` with `s² = k`, `s ≠ 0`, and an automorphism
`σ` with `σ s = −s` (the nontrivial automorphism). -/
structure QuadData (K : Type*) [Field K] [Algebra ℚ K] (k : ℚ) where
  /-- The square root `√k`. -/
  s : K
  hs : s ≠ 0
  hsk : s ^ 2 = algebraMap ℚ K k
  /-- The nontrivial automorphism `√k ↦ −√k`. -/
  σ : K ≃ₐ[ℚ] K
  hσ : σ s = -s

namespace QuadData

variable {K : Type*} [Field K] [NumberField K] {k : ℚ} (D : QuadData K k)

/-- `σ` is not the identity. PROVED. -/
theorem σ_ne_one : D.σ ≠ 1 := by
  intro h
  have h1 := D.hσ
  rw [h, AlgEquiv.one_apply] at h1
  have h2 : (2 : K) * D.s = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact two_ne_zero h3
  · exact D.hs h3

/-- `σ` is an involution (the Galois group of a quadratic extension has order two). PROVED. -/
theorem σ_σ [Algebra.IsQuadraticExtension ℚ K] (x : K) : D.σ (D.σ x) = x := by
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  have h2 : D.σ ^ 2 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have := congrArg (fun τ : K ≃ₐ[ℚ] K => τ x) h2
  simpa [pow_two] using this

end QuadData

/-! ### Conjugation of points and descent -/

section Conj

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] {k : ℚ} (D : QuadData K k)

/-- Conjugation of points by `σ`. -/
noncomputable abbrev conj {W : WeierstrassCurve ℚ} :
    (W.baseChange K).toAffine.Point →+ (W.baseChange K).toAffine.Point :=
  Point.map D.σ.toAlgHom

variable [Algebra.IsQuadraticExtension ℚ K]

/-- `σ` acts as an involution on points. PROVED. -/
theorem conj_conj {W : WeierstrassCurve ℚ} (P : (W.baseChange K).toAffine.Point) :
    conj D (conj D P) = P := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  · simp only [conj, Point.map_some, Point.some.injEq]
    exact ⟨D.σ_σ x, D.σ_σ y⟩

/-- The rational point whose base change is a given `σ`-invariant point. -/
noncomputable def descend {W : WeierstrassCurve ℚ} (R : (W.baseChange K).toAffine.Point)
    (hR : conj D R = R) : (W.baseChange ℚ).toAffine.Point :=
  Classical.choose (exists_baseChange_eq_of_map_eq D.σ_ne_one hR)

/-- The descended point base-changes back to the given point. PROVED. -/
theorem baseChange_descend {W : WeierstrassCurve ℚ} (R : (W.baseChange K).toAffine.Point)
    (hR : conj D R = R) : Point.baseChange ℚ K (descend D R hR) = R :=
  Classical.choose_spec (exists_baseChange_eq_of_map_eq D.σ_ne_one hR)

end Conj

/-! ### Points and the two maps -/

section SumDifference

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]
  (E : WeierstrassCurve ℚ) (h k : ℚ) (D : QuadData K k)

/-- The twist isomorphism `ι : E^{(hk)}_K ≃ E^{(h)}_K` attached to `D`. -/
noncomputable abbrev iota : ((qtwist E (h * k)).baseChange K).toAffine.Point ≃+
    ((qtwist E h).baseChange K).toAffine.Point :=
  twistAddEquiv E h k D.s D.hs D.hsk

omit [Algebra.IsQuadraticExtension ℚ K] in
/-- `σ(ι Y) = −ι(σ Y)`. PROVED. -/
theorem conj_iota (Y : ((qtwist E (h * k)).baseChange K).toAffine.Point) :
    conj D (iota E h k D Y) = -iota E h k D (conj D Y) :=
  map_twistAddEquiv E h k D.s D.hs D.hsk D.σ.toAlgHom D.hσ Y

/-- The difference `P − σP` is `σ`-anti-invariant, so `ι⁻¹(P − σP)` is `σ`-invariant. PROVED. -/
theorem conj_iota_symm_sub (P : ((qtwist E h).baseChange K).toAffine.Point) :
    conj D ((iota E h k D).symm (P - conj D P)) = (iota E h k D).symm (P - conj D P) := by
  set Y := (iota E h k D).symm (P - conj D P) with hY
  have hιY : iota E h k D Y = P - conj D P := by rw [hY, AddEquiv.apply_symm_apply]
  apply (iota E h k D).injective
  have h1 := conj_iota E h k D Y
  rw [hιY, map_sub, conj_conj] at h1
  -- h1 : σP - P = -ι(σY)
  rw [hιY]
  have h2 : iota E h k D (conj D Y) = -(conj D P - P) := by rw [h1, neg_neg]
  rw [h2, neg_sub]

/-- The sum `P + σP` is `σ`-invariant. PROVED. -/
theorem conj_add_conj (P : ((qtwist E h).baseChange K).toAffine.Point) :
    conj D (P + conj D P) = P + conj D P := by
  rw [map_add, conj_conj, add_comm]

/-- **The map `ψ : B(ℚ) → A(ℚ)`**, `(Q, R) ↦ Q_K + ι(R_K)`. -/
noncomputable def sumMap :
    ((qtwist E h).baseChange ℚ).toAffine.Point × ((qtwist E (h * k)).baseChange ℚ).toAffine.Point
      →+ ((qtwist E h).baseChange K).toAffine.Point :=
  (Point.baseChange ℚ K).comp (AddMonoidHom.fst _ _) +
    ((iota E h k D).toAddMonoidHom.comp (Point.baseChange ℚ K)).comp (AddMonoidHom.snd _ _)

omit [Algebra.IsQuadraticExtension ℚ K] in
theorem sumMap_apply (x : ((qtwist E h).baseChange ℚ).toAffine.Point ×
    ((qtwist E (h * k)).baseChange ℚ).toAffine.Point) :
    sumMap E h k D x = Point.baseChange ℚ K x.1 + iota E h k D (Point.baseChange ℚ K x.2) :=
  rfl

/-- **The map `φ : A(ℚ) → B(ℚ)`**, `P ↦ (P + σP, ι⁻¹(P − σP))`, each component descended
to `ℚ`. -/
noncomputable def diffMap : ((qtwist E h).baseChange K).toAffine.Point →+
    ((qtwist E h).baseChange ℚ).toAffine.Point × ((qtwist E (h * k)).baseChange ℚ).toAffine.Point
    where
  toFun P := (descend D (P + conj D P) (conj_add_conj E h k D P),
    descend D ((iota E h k D).symm (P - conj D P)) (conj_iota_symm_sub E h k D P))
  map_zero' := by
    ext
    · apply baseChange_injective (K := K)
      simp only [baseChange_descend, map_zero, add_zero, Prod.fst_zero]
    · apply baseChange_injective (K := K)
      simp only [baseChange_descend, map_zero, sub_zero, Prod.snd_zero]
  map_add' P P' := by
    ext
    · apply baseChange_injective (K := K)
      simp only [Prod.fst_add, map_add, baseChange_descend]
      abel
    · apply baseChange_injective (K := K)
      simp only [Prod.snd_add, map_add, baseChange_descend, map_sub]
      abel

theorem baseChange_diffMap_fst (P : ((qtwist E h).baseChange K).toAffine.Point) :
    Point.baseChange ℚ K (diffMap E h k D P).1 = P + conj D P :=
  baseChange_descend D _ (conj_add_conj E h k D P)

theorem baseChange_diffMap_snd (P : ((qtwist E h).baseChange K).toAffine.Point) :
    Point.baseChange ℚ K (diffMap E h k D P).2 = (iota E h k D).symm (P - conj D P) :=
  baseChange_descend D _ (conj_iota_symm_sub E h k D P)

/-- **`ψ ∘ φ = [2]`** (tex 4022–4023). PROVED. -/
theorem sumMap_diffMap (P : ((qtwist E h).baseChange K).toAffine.Point) :
    sumMap E h k D (diffMap E h k D P) = 2 • P := by
  rw [sumMap_apply, baseChange_diffMap_fst, baseChange_diffMap_snd, AddEquiv.apply_symm_apply,
    two_nsmul]
  abel

omit [Algebra.IsQuadraticExtension ℚ K] in
/-- `σ` fixes `Q_K` and negates `ι(R_K)`. PROVED. -/
theorem conj_sumMap (x : ((qtwist E h).baseChange ℚ).toAffine.Point ×
    ((qtwist E (h * k)).baseChange ℚ).toAffine.Point) :
    conj D (sumMap E h k D x) =
      Point.baseChange ℚ K x.1 - iota E h k D (Point.baseChange ℚ K x.2) := by
  rw [sumMap_apply, map_add, conj_iota, map_baseChange_eq, map_baseChange_eq, sub_eq_add_neg]

/-- **`φ ∘ ψ = [2]`** (tex 4022–4023). PROVED. -/
theorem diffMap_sumMap (x : ((qtwist E h).baseChange ℚ).toAffine.Point ×
    ((qtwist E (h * k)).baseChange ℚ).toAffine.Point) :
    diffMap E h k D (sumMap E h k D x) = 2 • x := by
  ext
  · apply baseChange_injective (K := K)
    rw [baseChange_diffMap_fst, conj_sumMap, sumMap_apply, Prod.smul_fst, map_nsmul, two_nsmul]
    abel
  · apply baseChange_injective (K := K)
    rw [baseChange_diffMap_snd, conj_sumMap, sumMap_apply, Prod.smul_snd, map_nsmul]
    apply (iota E h k D).injective
    rw [AddEquiv.apply_symm_apply, map_nsmul, two_nsmul]
    abel

/-! ### The height pairings of `A` and `B` and the adjunction -/

variable [(qtwist E h).IsElliptic] [(qtwist E (h * k)).IsElliptic]

/-- The height pairing of `A(ℚ) = E^{(h)}(K)`: the Néron–Tate pairing relative to `K`. -/
noncomputable def pairingA (P P' : ((qtwist E h).baseChange K).toAffine.Point) : ℝ :=
  ((qtwist E h).baseChange K).toAffine.neronTatePairing P P'

/-- The height pairing of `B(ℚ) = E^{(h)}(ℚ) × E^{(hk)}(ℚ)`: the sum of the Néron–Tate pairings. -/
noncomputable def pairingB (x x' : ((qtwist E h).baseChange ℚ).toAffine.Point ×
    ((qtwist E (h * k)).baseChange ℚ).toAffine.Point) : ℝ :=
  ((qtwist E h).baseChange ℚ).toAffine.neronTatePairing x.1 x'.1 +
    ((qtwist E (h * k)).baseChange ℚ).toAffine.neronTatePairing x.2 x'.2

/-- The canonical height of `B(ℚ)`: `ĥ_B(Q, R) = ĥ(Q) + ĥ(R)`. -/
noncomputable def heightB (x : ((qtwist E h).baseChange ℚ).toAffine.Point ×
    ((qtwist E (h * k)).baseChange ℚ).toAffine.Point) : ℝ :=
  x.1.canonicalHeight + x.2.canonicalHeight

theorem pairingB_self (x : ((qtwist E h).baseChange ℚ).toAffine.Point ×
    ((qtwist E (h * k)).baseChange ℚ).toAffine.Point) : pairingB E h k x x = heightB E h k x := by
  simp only [pairingB, heightB, neronTatePairing_self]

omit [Algebra.IsQuadraticExtension ℚ K] in
theorem pairingA_self (P : ((qtwist E h).baseChange K).toAffine.Point) :
    pairingA E h P P = P.canonicalHeight := by
  simp only [pairingA, neronTatePairing_self]

/-- **The adjunction**: `⟨φ P, x⟩_B = ⟨P, ψ x⟩_A` — the sum/difference isogenies are dual for the
height pairings of `A` and `B` (tex 4022–4023, 4027–4029). The proof uses
`⟨Q₁_K, Q₂_K⟩_K = 2 ⟨Q₁, Q₂⟩_ℚ` (`neronTatePairing_baseChange`, `[K : ℚ] = 2`), the Galois
invariance `⟨σX, σY⟩_K = ⟨X, Y⟩_K` (`neronTatePairing_map_algEquiv`) and the invariance of the
pairing under the twist isomorphism (`neronTatePairing_twistAddEquiv`). PROVED. -/
theorem pairingB_diffMap (P : ((qtwist E h).baseChange K).toAffine.Point)
    (x : ((qtwist E h).baseChange ℚ).toAffine.Point ×
      ((qtwist E (h * k)).baseChange ℚ).toAffine.Point) :
    pairingB E h k (diffMap E h k D P) x = pairingA E h P (sumMap E h k D x) := by
  have hn : (Module.finrank ℚ K : ℝ) = 2 := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two ℚ K]; norm_num
  obtain ⟨Q, R⟩ := x
  set Q' := (diffMap E h k D P).1 with hQ'
  set R' := (diffMap E h k D P).2 with hR'
  -- first component
  have e1 : ((qtwist E h).baseChange ℚ).toAffine.neronTatePairing Q' Q =
      pairingA E h P (Point.baseChange ℚ K Q) := by
    have hb := neronTatePairing_baseChange (K := K) (qtwist E h) Q' Q
    rw [hn, hQ', baseChange_diffMap_fst, neronTatePairing_add_left] at hb
    have hg : ((qtwist E h).baseChange K).toAffine.neronTatePairing (conj D P)
        (Point.baseChange ℚ K Q) =
        ((qtwist E h).baseChange K).toAffine.neronTatePairing P (Point.baseChange ℚ K Q) :=
      neronTatePairing_map_algEquiv_left (qtwist E h) D.σ P _ _ (map_baseChange_eq _ Q)
    rw [hg] at hb
    simp only [pairingA]
    linarith
  -- second component
  have e2 : ((qtwist E (h * k)).baseChange ℚ).toAffine.neronTatePairing R' R =
      pairingA E h P (iota E h k D (Point.baseChange ℚ K R)) := by
    have hb := neronTatePairing_baseChange (K := K) (qtwist E (h * k)) R' R
    rw [hn, ← neronTatePairing_twistAddEquiv E h k D.s D.hs D.hsk, hR',
      baseChange_diffMap_snd] at hb
    change ((qtwist E h).baseChange K).toAffine.neronTatePairing
        (iota E h k D ((iota E h k D).symm (P - conj D P)))
        (iota E h k D (Point.baseChange ℚ K R)) = _ at hb
    rw [AddEquiv.apply_symm_apply, neronTatePairing_sub_left] at hb
    -- `⟨σP, ι R_K⟩ = −⟨P, ι R_K⟩`
    have hfix : conj D (-iota E h k D (Point.baseChange ℚ K R)) =
        iota E h k D (Point.baseChange ℚ K R) := by
      rw [map_neg, conj_iota, map_baseChange_eq, neg_neg]
    have hg : ((qtwist E h).baseChange K).toAffine.neronTatePairing (conj D P)
        (iota E h k D (Point.baseChange ℚ K R)) =
        -((qtwist E h).baseChange K).toAffine.neronTatePairing P
          (iota E h k D (Point.baseChange ℚ K R)) := by
      rw [neronTatePairing_map_algEquiv_left (qtwist E h) D.σ P _ _ hfix,
        neronTatePairing_neg_right]
    rw [hg] at hb
    simp only [pairingA]
    linarith
  simp only [pairingB]
  rw [e1, e2, sumMap_apply]
  simp only [pairingA, neronTatePairing_add_right]

/-- **`ĥ_B(φ P) = 2 ĥ_A(P)`**. PROVED. -/
theorem heightB_diffMap (P : ((qtwist E h).baseChange K).toAffine.Point) :
    heightB E h k (diffMap E h k D P) = 2 * P.canonicalHeight := by
  rw [← pairingB_self, pairingB_diffMap, sumMap_diffMap, pairingA, two_nsmul,
    neronTatePairing_add_right, neronTatePairing_self]
  ring

/-- **`ĥ_A(ψ x) = 2 ĥ_B(x)`**. PROVED. -/
theorem heightA_sumMap (x : ((qtwist E h).baseChange ℚ).toAffine.Point ×
    ((qtwist E (h * k)).baseChange ℚ).toAffine.Point) :
    (sumMap E h k D x).canonicalHeight = 2 * heightB E h k x := by
  rw [← pairingA_self, ← pairingB_diffMap, diffMap_sumMap, ← pairingB_self]
  simp only [pairingB, two_nsmul, Prod.fst_add, Prod.snd_add, neronTatePairing_add_left]
  ring

/-! ### The regulator ratio in rank one -/

/-- The `B`-pairing kills torsion in its first argument. PROVED. -/
theorem pairingB_torsion_left
    {T : ((qtwist E h).baseChange ℚ).toAffine.Point ×
      ((qtwist E (h * k)).baseChange ℚ).toAffine.Point} (hT : IsOfFinAddOrder T)
    (x : ((qtwist E h).baseChange ℚ).toAffine.Point ×
      ((qtwist E (h * k)).baseChange ℚ).toAffine.Point) : pairingB E h k T x = 0 := by
  have h1 : IsOfFinAddOrder T.1 := (AddMonoidHom.fst _ _).isOfFinAddOrder hT
  have h2 : IsOfFinAddOrder T.2 := (AddMonoidHom.snd _ _).isOfFinAddOrder hT
  simp only [pairingB, neronTatePairing_eq_zero_of_isOfFinAddOrder_left h1,
    neronTatePairing_eq_zero_of_isOfFinAddOrder_left h2, add_zero]

/-- The `B`-pairing is additive in its first argument. PROVED. -/
theorem pairingB_add_left (x y z : ((qtwist E h).baseChange ℚ).toAffine.Point ×
    ((qtwist E (h * k)).baseChange ℚ).toAffine.Point) :
    pairingB E h k (x + y) z = pairingB E h k x z + pairingB E h k y z := by
  simp only [pairingB, Prod.fst_add, Prod.snd_add, neronTatePairing_add_left]
  ring

/-- The `B`-pairing is `ℤ`-linear in its first argument. PROVED. -/
theorem pairingB_zsmul_left (n : ℤ) (x z : ((qtwist E h).baseChange ℚ).toAffine.Point ×
    ((qtwist E (h * k)).baseChange ℚ).toAffine.Point) :
    pairingB E h k (n • x) z = n * pairingB E h k x z := by
  simp only [pairingB, Prod.smul_fst, Prod.smul_snd, neronTatePairing_zsmul_left]
  ring

/-- **The regulator ratio `Reg_B / Reg_A = 2/I²` and `IJ = 2`** (tex 4082–4091). Let `g_A`
generate `A(ℚ) = E^{(h)}(K)` modulo torsion and `g_B` generate `B(ℚ) = E^{(h)}(ℚ) × E^{(hk)}(ℚ)`
modulo torsion (rank one: an input, from the forward theorems at known simple zeros, tex 4020–4021).
Then there are integers `α, β` with `φ g_A ≡ α g_B` and `ψ g_B ≡ β g_A` modulo torsion, so that
`I = [B_free : φ A_free] = |α|` and `J = [A_free : ψ B_free] = |β|`, and
`αβ = 2` (`IJ = 2`), `α Reg_B = β Reg_A` (the adjunction read on generators: RC15's input `hadj`)
and `Reg_B α² = 2 Reg_A` for `Reg_A = ĥ_A(g_A)`, `Reg_B = ĥ_B(g_B)`. PROVED. -/
theorem regulator_ratio_sumDiff (gA : ((qtwist E h).baseChange K).toAffine.Point)
    (gB : ((qtwist E h).baseChange ℚ).toAffine.Point ×
      ((qtwist E (h * k)).baseChange ℚ).toAffine.Point)
    (hA : IsFreeGenerator gA) (hB : IsFreeGenerator gB) :
    ∃ α β : ℤ, IsOfFinAddOrder (diffMap E h k D gA - α • gB) ∧
      IsOfFinAddOrder (sumMap E h k D gB - β • gA) ∧ α * β = 2 ∧
      (α : ℝ) * heightB E h k gB = β * gA.canonicalHeight ∧
      heightB E h k gB * (α : ℝ) ^ 2 = 2 * gA.canonicalHeight := by
  obtain ⟨α, hα⟩ := hB.2 (diffMap E h k D gA)
  obtain ⟨β, hβ⟩ := hA.2 (sumMap E h k D gB)
  -- `αβ = 2`
  have hαβ : α * β = 2 := by
    have h1 : IsOfFinAddOrder (sumMap E h k D (diffMap E h k D gA - α • gB)) :=
      (sumMap E h k D).isOfFinAddOrder hα
    rw [map_sub, sumMap_diffMap, map_zsmul] at h1
    have h2 : IsOfFinAddOrder (α • (sumMap E h k D gB - β • gA)) := hβ.zsmul
    have h3 := h1.add h2
    have h4 : (2 • gA - α • sumMap E h k D gB) + α • (sumMap E h k D gB - β • gA) =
        (2 - α * β) • gA := by
      rw [smul_sub, sub_smul, mul_smul, two_nsmul, two_zsmul]
      abel
    rw [h4] at h3
    have := eq_zero_of_isOfFinAddOrder_zsmul hA.1 h3
    linarith
  -- `α Reg_B = β Reg_A`
  have hadj : (α : ℝ) * heightB E h k gB = β * gA.canonicalHeight := by
    have hl : pairingB E h k (diffMap E h k D gA) gB = α * heightB E h k gB := by
      have e : diffMap E h k D gA = (diffMap E h k D gA - α • gB) + α • gB := by abel
      rw [e, pairingB_add_left, pairingB_torsion_left E h k hα, pairingB_zsmul_left,
        pairingB_self, zero_add]
    have hr : pairingA E h gA (sumMap E h k D gB) = β * gA.canonicalHeight := by
      have e : sumMap E h k D gB = (sumMap E h k D gB - β • gA) + β • gA := by abel
      rw [e, pairingA, neronTatePairing_add_right,
        neronTatePairing_eq_zero_of_isOfFinAddOrder_right _ hβ, zero_add,
        neronTatePairing_zsmul_right, neronTatePairing_self]
    rw [← hl, ← hr, pairingB_diffMap]
  refine ⟨α, β, hα, hβ, hαβ, hadj, ?_⟩
  have hαβR : (α : ℝ) * β = 2 := by exact_mod_cast hαβ
  linear_combination (α : ℝ) * hadj + gA.canonicalHeight * hαβR

end SumDifference

end ZInQ.Manuscript.RC.Height
