import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitFamilyPin
import ZInQKernel.Contrib.CloudB3E1RingClass.MovingGenuine

/-!
# Theorem 5.3, Lane RC0 round 19: the family's moving character on the genuine ring class fields

Proposition `ex:arith-moving-character` (tex 3500–3702) as used at tex 2729–2737 and 4258–4268:
the moving character is a character of `Gal(H_r/K)`, `H_r` the ring class field of conductor `r`,
pulled back along the genuine restriction `G_{K,S_r} → Gal(H_r/K)`.

* `genuinePsi C r m ξ₀`: the composite of the genuine restriction of the ring-class setup `C` at
  `r` with an additive character `ξ₀` of `Gal(H_r/K)`.
* `GenuineFamilyMovingCharacter K ℓ Q`: the remaining inputs of the genuine moving character as
  named hypotheses: the ring-class setup `C` (the chosen primes over `2N` and over `Q`, the moving
  supports, the places over `r`), at every stage `i` the inputs `I i` of a genuine `MovingDataK`
  at precision `2i` (`GenuineMovingInputs`: the Kummer data, class group generators and relations,
  the ring-class exact sequence, the inertia identification and the Frobenius power-residue
  formula, with their kinds), the orientation index of each `q ∈ Q` and the covering of the places
  above `2N` by the chosen primes; and the chosen moving primes `r i` with characters
  `ξ₀ i` of `Gal(H_{r_i}/K)` whose pullbacks satisfy the properties of the genuine moving
  character (`moving_character_genuine`): open kernel, surjective on the genuine inertia group at
  the place over `r_i`, trivial on the genuine decomposition groups above `2N`, value `1` on every
  Frobenius lift at the orientations and `−1` at the conjugates.
* `GenuineFamilyMovingCharacter.toFamily` (PROVED): the family's moving character
  (`FamilyMovingCharacter`).
* `RegularityInputsILG`, `PrimRegularityInputsILG`: the leaf forms of `RegularityInputsILQ`,
  `PrimRegularityInputsILQ` with the family's character given by genuine data. PROVED:
  `PrimRegularityInputsILG.toILQ`, `primRegularityInputs_of_ILG`, `heightOneTarget_of_ILG`,
  `RegularityInputsILG.toMdl`, `primRegularityInputsILG_of_uPrim_zero`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.SelmerComplex (GKS Gloc locMap)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Manuscript.RC.TateWiring (GoodPrime)
open ZInQ.Contrib.CloudB3E1RingClass (RingClassSetup GenuineMovingInputs setupGal ringClassRes
  max_one_ne_zero)
open ZInQ.Contrib.CloudB3RC53.CST (newformLevel)

section Genuine

variable {K : Type} [Field K] [NumberField K]

/-- **The moving exponent through the genuine ring class field** (tex 3565–3595, 3679–3684): the
genuine restriction `G_{K,S_r} → Gal(H_r/K)` of the setup `C` followed by an additive character
`ξ₀` of `Gal(H_r/K)` with values in `ℤ/2^m`. Kind: definition. -/
def genuinePsi {s : ℕ} (C : RingClassSetup K s) (r m : ℕ)
    (ξ₀ : Additive (setupGal C r) →+ ZMod (2 ^ m)) :
    GKS K (C.Sr r) →* Multiplicative (ZMod (2 ^ m)) :=
  (AddMonoidHom.toMultiplicative ξ₀).comp
    (ringClassRes (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r))

variable (K) in
/-- **The family's moving character from genuine data** (tex 2729–2737, 3500–3702, 4258–4268),
for the orientation primes `Q`:
* `s`, `C`: the ring-class setup (the chosen primes `𝔭_j`, `𝔭̄_j` with `𝔭_j 𝔭̄_j = (p_j)`, the
  moving supports `C.Sr r` containing the places over `r`, a place over each `r`; data and GLUE);
* `I`: at every stage `i`, the remaining inputs of a genuine `MovingDataK` at precision `2i`
  (`GenuineMovingInputs`, with the kinds of its fields; tex 3530–3595, 3662–3693);
* `o`, `act_o`, `p_o`: the orientation of each `q ∈ Q` is an active chosen prime over `q`;
* `over2N`: the places above `2N` are chosen primes over `2N` (`K` split at `2N`, tex 2720);
* `Sr_finite`: the moving supports are finite;
* `r`, `r_prime`, `r_injective`, `r_notQ`, `r_not_twoN`, `r_good`: the moving primes, good for the
  inputs of their stage, injective, outside `Q` and prime to `2N` (tex 4268–4270);
* `ξ₀`: characters of `Gal(H_{r_i}/K)`, with the properties of the genuine moving character
  (`moving_character_genuine`) for their pullbacks `genuinePsi`: open kernel, surjective on the
  genuine inertia group at the place over `r_i`, trivial on the genuine decomposition groups
  above `2N`, value `1` on every Frobenius lift at the orientations and `−1` at the conjugates.
Kind: definition (named inputs). -/
structure GenuineFamilyMovingCharacter (ℓ : ℕ) (Q : Finset ℕ) where
  /-- The number of chosen primes. -/
  s : ℕ
  /-- The ring-class setup. -/
  C : RingClassSetup K s
  /-- The remaining inputs of the genuine moving data at each stage. -/
  I : ∀ i, GenuineMovingInputs (Ecurve ℓ) (2 * i) C
  /-- The orientation index of each prime of `Q`. -/
  o : ℕ → Fin s
  /-- The orientations are active at every stage. -/
  act_o : ∀ i, ∀ q ∈ Q, (I i).act (o q)
  /-- The orientation of `q` lies over `q`. -/
  p_o : ∀ q ∈ Q, C.p (o q) = q
  /-- The places above `2N` are chosen primes over `2N`. -/
  over2N : ∀ i, ∀ v ∈ placesTwoN K ℓ, ∃ j, (I i).over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j)
  /-- The moving supports are finite. -/
  Sr_finite : ∀ r, (C.Sr r).Finite
  /-- The moving primes. -/
  r : ℕ → ℕ
  /-- They are prime. -/
  r_prime : ∀ i, (r i).Prime
  /-- They vary with the stage. -/
  r_injective : Function.Injective r
  /-- They are outside `Q`. -/
  r_notQ : ∀ i, r i ∉ Q
  /-- They do not divide `2N`. -/
  r_not_twoN : ∀ i, ¬ r i ∣ 2 * newformLevel (Ecurve ℓ)
  /-- They are good for the inputs of their stage. -/
  r_good : ∀ i, GoodPrime (Ecurve ℓ) (I i).sqrtD (I i).Sexc (r i)
  /-- The characters of `Gal(H_{r_i}/K)`. -/
  ξ₀ : ∀ i, Additive (setupGal C (r i)) →+ ZMod (2 ^ (2 * i))
  /-- Their pullbacks have open kernels. -/
  ψ_open : ∀ i, IsOpen ((genuinePsi C (r i) (2 * i) (ξ₀ i)).ker : Set (GKS K (C.Sr (r i))))
  /-- Surjective on the genuine inertia group at the place over `r_i`. -/
  inertia_onto : ∀ i, ∀ y : ZMod (2 ^ (2 * i)),
    ∃ σ ∈ TauCeti.inertiaSubgroup ((C.placeR (r i)).adicCompletion K),
      genuinePsi C (r i) (2 * i) (ξ₀ i) (locMap K (C.Sr (r i)) (C.placeR (r i)) σ) =
        Multiplicative.ofAdd y
  /-- Trivial on the genuine decomposition groups above `2N`. -/
  twoN : ∀ i, ∀ v ∈ placesTwoN K ℓ, ∀ σ : Gloc K v,
    genuinePsi C (r i) (2 * i) (ξ₀ i) (locMap K (C.Sr (r i)) v σ) = 1
  /-- Value `1` on every Frobenius lift at the orientations. -/
  orient_one : ∀ i, ∀ q ∈ Q, ∀ φ : Gloc K (C.𝔭 (o q)),
    TauCeti.IsArithFrobeniusLift ((C.𝔭 (o q)).adicCompletion K) φ →
      genuinePsi C (r i) (2 * i) (ξ₀ i) (locMap K (C.Sr (r i)) (C.𝔭 (o q)) φ) =
        Multiplicative.ofAdd 1
  /-- Value `−1` on every Frobenius lift at the conjugate orientations. -/
  orientBar_neg : ∀ i, ∀ q ∈ Q, ∀ φ : Gloc K (C.𝔭bar (o q)),
    TauCeti.IsArithFrobeniusLift ((C.𝔭bar (o q)).adicCompletion K) φ →
      genuinePsi C (r i) (2 * i) (ξ₀ i) (locMap K (C.Sr (r i)) (C.𝔭bar (o q)) φ) =
        Multiplicative.ofAdd (-1)

variable {ℓ : ℕ} {Q : Finset ℕ}

/-- The chosen prime over `p_j` contains `p_j`. Kind: PROVED. -/
theorem ringClassSetup_p_mem_𝔭 {s : ℕ} (C : RingClassSetup K s) (j : Fin s) :
    (((C.p j : ℤ)) : 𝓞 K) ∈ (C.𝔭 j).asIdeal := by
  have h : (((C.p j : ℤ)) : 𝓞 K) ∈ (C.𝔭 j).asIdeal * (C.𝔭bar j).asIdeal := by
    rw [C.𝔭_mul]
    exact Ideal.mem_span_singleton_self _
  exact (Ideal.mul_le_left : (C.𝔭 j).asIdeal * (C.𝔭bar j).asIdeal ≤ (C.𝔭 j).asIdeal) h

/-- The conjugate chosen prime over `p_j` contains `p_j`. Kind: PROVED. -/
theorem ringClassSetup_p_mem_𝔭bar {s : ℕ} (C : RingClassSetup K s) (j : Fin s) :
    (((C.p j : ℤ)) : 𝓞 K) ∈ (C.𝔭bar j).asIdeal := by
  have h : (((C.p j : ℤ)) : 𝓞 K) ∈ (C.𝔭 j).asIdeal * (C.𝔭bar j).asIdeal := by
    rw [C.𝔭_mul]
    exact Ideal.mem_span_singleton_self _
  exact (Ideal.mul_le_right : (C.𝔭 j).asIdeal * (C.𝔭bar j).asIdeal ≤ (C.𝔭bar j).asIdeal) h

/-- **The family's moving character of genuine data** (`FamilyMovingCharacter`): the moving
supports `C.Sr (r i)`, the exponents `genuinePsi`, the places over `r_i` of the setup, and the
chosen primes over `Q` and their conjugates as orientations. Kind: PROVED. -/
def GenuineFamilyMovingCharacter.toFamily (G : GenuineFamilyMovingCharacter K ℓ Q) :
    FamilyMovingCharacter K ℓ Q where
  r := G.r
  r_prime := G.r_prime
  r_injective := G.r_injective
  r_notQ := G.r_notQ
  r_not_twoN := G.r_not_twoN
  Sr i := G.C.Sr (G.r i)
  Sr_finite i := G.Sr_finite (G.r i)
  Sr_r i v hv := by
    apply G.C.hSr (G.r i) v
    have hr1 : max (G.r i) 1 = G.r i := max_eq_left (G.r_prime i).one_lt.le
    rw [hr1]
    simpa [placesOf] using hv
  ψ i := genuinePsi G.C (G.r i) (2 * i) (G.ξ₀ i)
  ψ_open := G.ψ_open
  twoN := G.twoN
  placeR i := G.C.placeR (G.r i)
  placeR_over i := (G.I i).placeR_over (G.r i) (G.r_good i)
  inertia_onto := G.inertia_onto
  orient q := G.C.𝔭 (G.o q)
  orient_over q hq := by
    have h := ringClassSetup_p_mem_𝔭 G.C (G.o q)
    rw [G.p_o q hq] at h
    exact h
  orient_one := G.orient_one
  orientBar q := G.C.𝔭bar (G.o q)
  orientBar_over q hq := by
    have h := ringClassSetup_p_mem_𝔭bar G.C (G.o q)
    rw [G.p_o q hq] at h
    exact h
  orientBar_neg := G.orientBar_neg

end Genuine

section Leaf

/-- **The per-instance form over genuine data** (for the ring instances of (3.5)): `u = 0`, or
the field data and the instance's moving character from genuine data over the primes of `h`,
chosen once, with the address clause. Kind: definition. -/
def RegularityInputsILG (ℓ : ℕ) (h k : ℤ) (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
    (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W),
    W = (Ecurve ℓ).baseChange K ∧ Module.finrank ℚ K = 2 ∧ (∃ sk : K, sk ^ 2 = (k : K)) ∧
    ∃ G : GenuineFamilyMovingCharacter K ℓ h.natAbs.primeFactors,
      RegularityInputsILQFam Cn hW G.toFamily h u

/-- The genuine per-instance form gives the abstract one. Kind: PROVED. -/
theorem RegularityInputsILG.toILQ {ℓ : ℕ} {h k : ℤ} {u : FractionRing Lambda}
    (hI : RegularityInputsILG ℓ h k u) : RegularityInputsILQ ℓ h k u := by
  rcases hI with hI | ⟨K, i1, i2, S, Cn, W, hW, i3, i4, hWE, hK2, hk, G, hF⟩
  · exact Or.inl hI
  · exact Or.inr ⟨K, i1, i2, S, Cn, W, hW, i3, i4, hWE, hK2, hk, G.toFamily, hF⟩

/-- The genuine per-instance form gives the model-level inputs. Kind: PROVED. -/
theorem RegularityInputsILG.toMdl {ℓ : ℕ} {h k : ℤ} {u : FractionRing Lambda}
    (hI : RegularityInputsILG ℓ h k u) : RegularityInputsMdl u :=
  hI.toILQ.toMdl

variable {ℓ : ℕ} (D : RCData ℓ)

/-- **The height-one leaf over the family's genuine moving character** (tex 4976–5200, at the
final families; F1 bound to the genuine ring-class character, F2): as `PrimRegularityInputsILQ`,
with the family's moving character given by genuine data (`GenuineFamilyMovingCharacter`, whose
fields are the remaining inputs of the genuine moving character as named hypotheses).
Kind: definition. -/
def PrimRegularityInputsILG : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∃ U : Addr F.b → FractionRing Lambda, (∀ x, IsTExpansion (U x) (D.uPrim F x)) ∧
      ((∀ x, U x = 0) ∨
        ∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
          (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
          (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W),
          W = (Ecurve ℓ).baseChange K ∧ Module.finrank ℚ K = 2 ∧
          (∃ sk : K, sk ^ 2 = (D.kfin : K)) ∧
          ∃ G : GenuineFamilyMovingCharacter K ℓ F.Q,
            ∀ x, RegularityInputsILQFam Cn hW G.toFamily (F.h x) (U x))

/-- The genuine leaf gives the abstract leaf. Kind: PROVED. -/
theorem PrimRegularityInputsILG.toILQ (hI : PrimRegularityInputsILG D) :
    PrimRegularityInputsILQ D := by
  intro Co Ce F hF
  obtain ⟨U, hT, hU⟩ := hI Co Ce F hF
  refine ⟨U, hT, ?_⟩
  rcases hU with hU | ⟨K, i1, i2, S, Cn, W, hW, i3, i4, hWE, hK2, hk, G, hx⟩
  · exact Or.inl hU
  · exact Or.inr ⟨K, i1, i2, S, Cn, W, hW, i3, i4, hWE, hK2, hk, G.toFamily, hx⟩

/-- **`PrimRegularityInputs` from the genuine leaf**. Kind: PROVED. -/
theorem primRegularityInputs_of_ILG (hI : PrimRegularityInputsILG D) : PrimRegularityInputs D :=
  primRegularityInputs_of_ILQ D hI.toILQ

/-- **`RCSteps.height_one`** from the genuine leaf and (4.7). Kind: PROVED (from the inputs). -/
theorem heightOneTarget_of_ILG (hI : PrimRegularityInputsILG D) (h47 : CommonCoordinateTarget D) :
    HeightOneTarget D :=
  heightOneTarget_of_ILQ D hI.toILQ h47

/-- **Degenerate satisfiability**: the genuine leaf holds when the primitive coordinates vanish.
Kind: PROVED. -/
theorem primRegularityInputsILG_of_uPrim_zero (hD : ∀ F x, D.uPrim F x = 0) :
    PrimRegularityInputsILG D :=
  fun _ _ F _ => ⟨fun _ => 0, fun x => by rw [hD F x]; exact isTExpansion_zero,
    Or.inl fun _ => rfl⟩

end Leaf

end ZInQ.Manuscript.RC.Wiring
