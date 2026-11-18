import ZInQKernel.Contrib.OneProof.RC.Wiring.Data
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.HeightDischarge

/-!
# Theorem 5.3, Lane RC0 round 2: (3.4) from the shared layer's GenusOdd at the genuine objects

The shared layer's GenusOdd proves (3.4) at every rough companion (`gzEveryCompanion_of_RC19`, with
`C_per = 0`) from `Prints` and the GLUE left after lane RC19 (`GlueAfterRC19`: Artin factorization,
genus theory, the splitting criterion), for the genuine objects: `L_* = LstarQ` (the normalized
twisted central value over a lattice of `E`), `j_gen`, `j_rc` read off selections of Heegner data,
the prepared filter `Prepared`, the genus partner `GenusPartner` and the rough companion relation
`Companion`.

`gz34Target_of_genusOdd` (PROVED) gives this file's `Gz34Target` (both clauses: the rough companions
and the final `k`) from such an instance (`GenusOddInstance`): the identification of the interface
data with the genuine objects, the CST data of `E`, the Heegner selections, and the final `k`'s
conditions (`k ≡ 1 (mod 4)`, a unit square at `2N`, prime to `h_*`, recorded by `RCSteps.companion`).
It is an alternative discharge of the leaf `PreLeaves.gz34`; using it in `RCLeaves` requires lane
RC11's normalization of `L_*` (`PreLeaves.lstar`) to be `LstarQ` at the same lattice, which is not
checked here.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

/-- **An instance of the shared layer's genuine objects of (3.4) for the interface data `W`**
(tex 2343–2353, 2403–2440, 2595–2603). Kinds: definitions (the identifications `prepared`,
`Lstar`, `jgen`, `jrc`, `companion`), the CST data of `E` (definition: newform, lattice,
parametrization scale), Elkik/Manin–Drinfeld rationality of `L_*(h_*)` (PRINT application), the
Heegner selections (definition: Heegner points exist at prepared simple zeros, CST's hypotheses),
and the final `k`'s conditions (ELLIOT, as in `RCSteps.companion`). Owner: batch 3 GenusOdd with
RC11 (normalization) and RC13 (companions). -/
structure GenusOddInstance {ℓ : ℕ} (W : WData ℓ) : Type 1 where
  hE : (Ecurve ℓ).IsElliptic
  f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) : Subgroup (GL (Fin 2) ℝ)) 2
  hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ)
  Lat : PeriodPair
  hLat : IsLatticeOf (Ecurve ℓ) Lat
  hNC : IsNonCMLattice Lat
  κ : ℂ
  hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ
  /-- `h_*` is a genus partner in the shared layer's sense -/
  hgp : GenusPartner (Ecurve ℓ) W.hstar
  /-- `L_*(h_*)` is rational (Elkik, Manin–Drinfeld) -/
  hElkikMD : ∃ q : ℚ, (q : ℂ) = Lstar (Ecurve ℓ) Lat W.hstar
  selG : (h : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (h * W.hstar) 1 W.hstar)
  selR : (h k : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ k h.natAbs h)
  hselG : ∀ h, Prepared (Ecurve ℓ) W.hstar h → AnalyticRank (qtwist (Ecurve ℓ) h) 1 →
    (selG h).isSome
  hselR : ∀ h k', Prepared (Ecurve ℓ) W.hstar h → AnalyticRank (qtwist (Ecurve ℓ) h) 1 →
    Companion (Ecurve ℓ) Lat W.hstar h k' → (selR h k').isSome
  /-- the prepared filter is the shared layer's -/
  hprep : ∀ h, W.prepared h → Prepared (Ecurve ℓ) W.hstar h
  /-- `L_*` is the shared layer's `LstarQ` -/
  hLs : W.Lstar = LstarQ (Ecurve ℓ) Lat
  /-- `j_gen` is read off the genus selections -/
  hjg : W.jgen = jgenOf (Ecurve ℓ) f Lat κ W.hstar selG
  /-- `j_rc` is read off the ring-class selections -/
  hjr : W.jrc = jrcOf (Ecurve ℓ) f Lat κ selR
  /-- a rough companion is a companion in the shared layer's sense -/
  hcomp : ∀ h k', W.IsRoughCompanion h k' → Companion (Ecurve ℓ) Lat W.hstar h k'
  /-- the final `k`: negative, squarefree, `≡ 1 (mod 4)`, a unit square at `2N`, prime to `h_*` -/
  hk0 : W.kfin < 0
  hksq : Squarefree W.kfin
  hk4 : W.kfin % 4 = 1
  hk2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → UnitSquareAt p W.kfin
  hkcop : IsCoprime W.kfin W.hstar

/-- **(3.4) with one period constant (`C_per = 0`)** from the shared layer's GenusOdd (PROVED from
`gzEveryCompanion_of_RC19`). The final `k` is a companion of every prepared simple zero `h` with
`L_*(hk) ≠ 0` whose primes are outside the support with `(k/q) = 1`: at the primes of `2N` by the
recorded squares, at the primes of `h` by `(k/q) = 1` (`h` is odd, being `≡ 1 (mod 8)`). -/
theorem gz34Target_of_genusOdd {ℓ : ℕ} {W : WData ℓ} (P : Prints) (G : GlueAfterRC19)
    (I : GenusOddInstance W) : Gz34Target W := by
  have := I.hE
  have hall := gzEveryCompanion_of_RC19 P G (E := Ecurve ℓ) rfl rfl I.hf I.hLat I.hNC I.hκ I.hgp
    I.hElkikMD I.selG I.selR I.hselG I.hselR
  refine ⟨0, fun h k' hp hz hk => ?_, fun h hp hz hL hq => ?_⟩
  · have := hall h k' (I.hprep h hp) hz (I.hcomp h k' hk)
    rwa [I.hLs, I.hjg, I.hjr]
  · have hP := I.hprep h hp
    -- `L_*(hk) ≠ 0` for the genuine `L_*`
    have hLQ : LstarQ (Ecurve ℓ) I.Lat (h * W.kfin) ≠ 0 := by rwa [I.hLs] at hL
    have hLC : Lstar (Ecurve ℓ) I.Lat (h * W.kfin) ≠ 0 := by
      rw [← LstarQ_spec hLQ]; exact_mod_cast hLQ
    -- `h` is odd
    have h2N2 : 2 ∣ 2 * newformLevel (Ecurve ℓ) := dvd_mul_right 2 _
    have hh2 : ¬ (2 : ℤ) ∣ h := (hP.2.2.1 2 Nat.prime_two h2N2).1
    have hcompk : Companion (Ecurve ℓ) I.Lat W.hstar h W.kfin := by
      refine ⟨I.hk0, I.hk4, I.hksq, fun p hp' hpd => ?_, I.hkcop, hLC⟩
      have hpd' : (p : ℤ) ∣ ((2 * newformLevel (Ecurve ℓ) : ℕ) : ℤ) * h := by
        exact_mod_cast hpd
      rcases (Int.prime_iff_natAbs_prime.mpr (by simpa using hp')).dvd_mul.mp hpd' with h1 | h1
      · exact I.hk2N p hp' (Int.natCast_dvd_natCast.mp h1)
      · have hp2 : p ≠ 2 := by
          rintro rfl
          exact hh2 (by exact_mod_cast h1)
        exact squareAt_of_jacobiSym hp' hp2 (hq p hp' h1).2
    have := hall h W.kfin hP hz hcompk
    rwa [I.hLs, I.hjg, I.hjr]

end ZInQ.Manuscript.RC.Wiring
