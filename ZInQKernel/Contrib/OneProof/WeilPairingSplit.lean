import ZInQKernel.OneProof.H.TailZ24

/-! # The Weil pairing leaf `weilPairingMumford`, one printed property per leaf

Task t09-pic (docs/research/t09-pic.md, "L4 split into one printed property per leaf"), copied verbatim from
`scratch/t09-pic/Pic.lean`. The leaf `T09Pic.WeilPairingMumford` (TailZ24) bundles six printed properties of
Mumford's pairing `ē_n`, pinned to the genuine `weilScalar`. Here each property is its own leaf (L4a-f), and
`weilPairingMumford_of_split` recovers the bundled leaf, so the fold replaces one composite leaf by six printed ones.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace T09Pic.Split

open PkgI3 PkgI3.AbVar _root_.T09Pic HDec.WeilPairing

variable {K : Type} [Field K]

/-- `e` is Mumford's pairing: its values are `weilScalar` (as constants of `Γ(A_K̄, 𝒪)`) for every
`n ≥ 1` invertible in `K`. Since `constK` is injective, this pins `e n` for those `n`. -/
def IsMumfordPairing {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n) : Prop :=
  ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ (x : tors A n) (y : tors B n),
    constK A ((e n x y).val : AlgebraicClosure K) =
      weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A)) (Additive.toMul (y : HDec.WeilPairing.P B))

/-- **LEAF L4a (`ē_n` is a bilinear `μ_n`-valued pairing).** Mumford §20 (definition of `ē_n`;
values in `μ_n`, bilinear), with Kleiman 9.2.5 and Mumford §8 (iv); UNVERIFIED numbering. -/
def WeilPairingExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j → ∃ e : ∀ n : ℕ, Pairing A B n, IsMumfordPairing rep j e

/-- **LEAF L4b (`ē_n` is perfect).** Mumford §20 (n prime to the characteristic); UNVERIFIED. -/
def WeilPairingPerfect : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsPerfect (e n)

/-- **LEAF L4c (`ē_n` is Galois-equivariant).** `ē_n` is defined over `K` (Milne 1986 §16);
UNVERIFIED. -/
def WeilPairingGalois : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → HDec.WeilPairing.IsGalEquivariant (e n)

/-- **LEAF L4d (compatibility `ē_{mn}(x, y) = ē_n(mx, y)` for `y ∈ Â[n]`).** Mumford §20;
UNVERIFIED. -/
def WeilPairingCompat : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ m n : ℕ, 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
      ∀ (x : tors A (m * n)) (y : tors B n),
        (e (m * n) x (torsIncl B (dvd_mul_left n m) y)).val = (e n (torsSmul A m n x) y).val

/-- **LEAF L4e (adjunction `ē_n(x, f^∨ y) = ē_n(f x, y)`).** Mumford §20 (5) for isogenies;
Milne 1986 Lemma 16.2(c) for all homomorphisms; UNVERIFIED. -/
def WeilPairingDual : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ (f : End A) (fv : End B), fv.hom ≫ j = j ≫ dualP rep f.hom → ∀ n : ℕ, 0 < n →
      (n : K) ≠ 0 → ∀ x y, e n x (torsMap fv n y) = e n (torsMap f n x) y

/-- **LEAF L4f (`e^L_n(x, x) = 1`).** Mumford §23 (`e^L_n(x, y) = ē_n(x, φ_L(y))` is
skew-symmetric with `e^L_n(x, x) = 1`; stated for ample `L`); UNVERIFIED. -/
def WeilPairingAlternating : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ L : A.X.left.Pic, IsAmple A.X.left L → ∀ lam : Hom A B, lam.hom ≫ j = phiL rep L →
      ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x : tors A n, e n x (torsMap lam n x) = 0

/-- The six split leaves give `WeilPairingMumford`. -/
theorem weilPairingMumford_of_split (ha : WeilPairingExists) (hb : WeilPairingPerfect)
    (hc : WeilPairingGalois) (hd : WeilPairingCompat) (he : WeilPairingDual)
    (hf : WeilPairingAlternating) : WeilPairingMumford := by
  intro K _ A P rep B j hj
  obtain ⟨e, hM⟩ := ha K A P rep B j hj
  exact ⟨e, hb K A P rep B j e hj hM, hc K A P rep B j e hj hM, hd K A P rep B j e hj hM,
    he K A P rep B j e hj hM, hf K A P rep B j e hj hM, hM⟩

end T09Pic.Split
