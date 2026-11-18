import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenericCoords
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.ActualComplements
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthPlaces
import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.StageInputs


/-!
# Strict and relaxed derivative conditions

The strict condition retains the zero-cocycles. The relaxed condition is the
truncation through degree one, not the full local complex. Their complement
comparison is proved over every self-injective commutative coefficient ring
from full local duality, by an explicit chase of the comparison cone.

Degree-zero cohomology is not removed. The final shape theorem identifies the
conditions at the switch place in the field-valued switching family.
-/

set_option maxHeartbeats 600000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.OldOrthogonality.Truncations

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy)

section Trunc01

variable {k : Type} [CommRing k]

theorem dual_factor_of_ker [Module.Injective k k] {V W : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (g : V →ₗ[k] W) (f : V →ₗ[k] k) (h : ∀ v, g v = 0 → f v = 0) :
    ∃ z : W →ₗ[k] k, ∀ v, z (g v) = f v := by
  have hinj : Function.Injective ((LinearMap.ker g).liftQ g le_rfl) := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  obtain ⟨z, hz⟩ := Module.Injective.out _ hinj ((LinearMap.ker g).liftQ f (fun v hv => h v hv))
  exact ⟨z, fun v => hz (Submodule.Quotient.mk v)⟩

theorem dual_extend_of_injective [Module.Injective k k] {V W : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (ι : V →ₗ[k] W) (hι : Function.Injective ι) (φ : V →ₗ[k] k) :
    ∃ z : W →ₗ[k] k, ∀ v, z (ι v) = φ v :=
  Module.Injective.out ι hι φ

structure TruncShape01 {U U' L L' : GCx k} (iU : GHom U L) (iU' : GHom U' L') : Prop where
                                      
  hLneg : ∀ n, n < 0 → Subsingleton (L.X n)
                                       
  hL'neg : ∀ n, n < 0 → Subsingleton (L'.X n)
                             
  hUz : ∀ n, n ≠ 0 → Subsingleton (U.X n)
                                  
  hU'z : ∀ n, n ≠ 0 → n ≠ 1 → Subsingleton (U'.X n)
                       
  hUinj : ∀ n m (h : n = m), Function.Injective (iU.f n m h)
                                
  hU0 : ∀ n m (h : n = m) m' (h' : m + 1 = m'), n = 0 → ∀ x : L.X m, L.d m m' h' x = 0 →
    ∃ u, iU.f n m h u = x
                        
  hU'inj : ∀ n, Function.Injective (iU'.f n n rfl)
                                 
  hU'0 : ∀ n, n = 0 → Function.Surjective (iU'.f n n rfl)
                                 
  hU'1 : ∀ n m (h : n + 1 = m), n = 1 → ∀ y : L'.X n, L'.d n m h y = 0 →
    ∃ y₁, iU'.f n n rfl y₁ = y

variable {U U' L L' E : GCx k} (iU : GHom U L) (iU' : GHom U' L')
  (P : GPair L L' E) (J : LocalTruncIsotropy iU iU' P) (trv : E.X 2 →ₗ[k] k)
  (htrv : ∀ z, trv (E.d 1 2 rfl z) = 0)

theorem trunc01_finish (htrv2 : ∀ z, trv (E.d (2 - 1) 2 (by omega) z) = 0)
    (hacyc : GAcyclic (coneCx (adjHom P 2 trv htrv2)))
    (hUz : ∀ n, n ≠ 0 → Subsingleton (U.X n))
    (i j l : ℤ) (hij : i + 1 = j) (hjl : j + 1 = l) (hj : 2 ≤ j)
    (u : U.X j) (x : L.X (j - 1)) (φ : (dualCx U' 3).X (j - 1))
    (hc : (coneCx (orthLocalMap iU iU' P J trv htrv)).d j l hjl
      ((((u, x) : coneT (orthNeg iU) j), φ) : coneT (orthLocalMap iU iU' P J trv htrv) j) = 0)
    (z : Module.Dual k (L'.X (3 - (j - 1))))
    (ha : ∀ y : U'.X (3 - (j - 1)), z (iU'.f _ _ rfl y) = asDual φ y)
    (hb : ∀ y : L'.X (3 - (l - 1)), trv (P.P (j - 1) (3 - (l - 1)) 2 (by omega) x y) =
      ZInQ.Contrib.CloudB3RC53.PairedFunctional.sgn (j - 2) • z (L'.d (3 - (l - 1)) (3 - (j - 1)) (by omega) y)) :
    ∃ c', (coneCx (orthLocalMap iU iU' P J trv htrv)).d i j hij c' =
      ((((u, x) : coneT (orthNeg iU) j), φ) : coneT (orthLocalMap iU iU' P J trv htrv) j) := by
  have := hUz j (by omega)
  have hu : u = 0 := Subsingleton.elim _ _
  have h1 : (orthNeg iU).f j (l - 1) (by omega) u - L.d (j - 1) (l - 1) (by omega) x = 0 :=
    congrArg (fun w => w.1.2) hc
  rw [hu, map_zero, zero_sub, neg_eq_zero] at h1
  have he : L.d (j - 1) (l - 1) (by omega) (-x) = 0 := by rw [map_neg, h1, neg_zero]
  have hz : ∀ y : L'.X (3 - (l - 1)), trv (P.P (j - 1) (3 - (l - 1)) 2 (by omega) (-x) y) =
      (-(ZInQ.Contrib.CloudB3RC53.PairedFunctional.sgn (j - 1 - 1))) • z (L'.d (3 - (l - 1)) (3 - (j - 1)) (by omega) y) := by
    intro y
    rw [show j - 1 - 1 = j - 2 by ring, LinearMap.map_neg₂, map_neg, hb y, neg_smul]
  obtain ⟨e', z', he', hz'⟩ := coneAdj_solve P trv htrv2 hacyc (i - 1) (j - 1) (l - 1) (by omega)
    (by omega) (3 - (l - 1)) (3 - (j - 1)) (3 - (i - 1)) (by omega) (by omega) (by omega) (-x) z he hz
  let φ' : Module.Dual k (U'.X (3 - (i - 1))) := -(z'.comp (iU'.f (3 - (i - 1)) (3 - (i - 1)) rfl))
  refine ⟨((((0 : U.X i), e') : coneT (orthNeg iU) i), φ'), ?_⟩
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · change U.d i j hij 0 = u
    rw [map_zero, hu]
  · change (orthNeg iU).f i (j - 1) (by omega) 0 - L.d (i - 1) (j - 1) (by omega) e' = x
    rw [map_zero, zero_sub, he', neg_neg]
  · refine dualCx_ext fun y => ?_
    change asDual ((orthLocalMap iU iU' P J trv htrv).f i (j - 1) (by omega)
        ((0, e') : coneT (orthNeg iU) i)) y -
      asDual ((dualCx U' 3).d (i - 1) (j - 1) (by omega) φ') y = asDual φ y
    rw [orthLocalMap_apply, LinearMap.map_zero₂, add_zero]
    erw [dualCx_d_apply]
    have hcomm := iU'.comm (3 - (j - 1)) (3 - (i - 1)) (3 - (j - 1)) (3 - (i - 1)) rfl (by omega)
      (by omega) rfl y
    have h3 : asDual φ' (U'.d (3 - (j - 1)) (3 - (i - 1)) (by omega) y) =
        -z' (L'.d (3 - (j - 1)) (3 - (i - 1)) (by omega) (iU'.f _ _ rfl y)) := by
      change -(z' (iU'.f (3 - (i - 1)) (3 - (i - 1)) rfl
        (U'.d (3 - (j - 1)) (3 - (i - 1)) _ y))) = _
      rw [hcomm]
    rw [h3, ← ha y, ← hz' (iU'.f _ _ rfl y), sgn_pred (i - 1)]
    simp only [zsmul_eq_mul, Int.cast_neg, smul_neg, neg_neg]
    ring

theorem trunc01_quasiIso [Module.Injective k k] (htrv2 : ∀ z, trv (E.d (2 - 1) 2 (by omega) z) = 0)
    (hacyc : GAcyclic (coneCx (adjHom P 2 trv htrv2)))
    (hS : TruncShape01 iU iU') :
    QuasiIso (GHom.toCC (orthLocalMap iU iU' P J trv htrv)) := by
  obtain ⟨hLneg, hL'neg, hUz, hU'z, hUinj, hU0, hU'inj, hU'0, hU'1⟩ := hS
  refine quasiIso_of_coneCx_acyclic _ (fun i j l hij hjl c hc => ?_)
  obtain ⟨⟨u, x⟩, φ⟩ := c
  have h1 : (orthNeg iU).f j (l - 1) (by omega) u - L.d (j - 1) (l - 1) (by omega) x = 0 :=
    congrArg (fun w => w.1.2) hc
  have h2 : ∀ y : U'.X (3 - (l - 1)),
      trv (P.P (j - 1) (3 - (l - 1)) 2 (by omega) x (iU'.f _ _ rfl y) +
        J.h j (3 - (l - 1)) 2 (by omega) u y) =
      (-(ZInQ.Contrib.CloudB3RC53.PairedFunctional.sgn (j - 1))) • asDual φ (U'.d (3 - (l - 1)) (3 - (j - 1)) (by omega) y) := by
    intro y
    have h : asDual ((orthLocalMap iU iU' P J trv htrv).f j (l - 1) (by omega)
        ((u, x) : coneT (orthNeg iU) j)) y -
        asDual ((dualCx U' 3).d (j - 1) (l - 1) (by omega) φ) y = 0 :=
      LinearMap.congr_fun (congrArg Prod.snd hc) y
    erw [orthLocalMap_apply, dualCx_d_apply] at h
    exact sub_eq_zero.mp h
  rcases (show j ≤ 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with hj | hj | hj | hj
  · 
    have hx : x = 0 := (hLneg (j - 1) (by omega)).elim _ _
    have hu : u = 0 := by
      by_cases hj0 : j = 0
      · rw [hx, map_zero, sub_zero, orthNeg_f_apply, neg_eq_zero] at h1
        exact hUinj j (l - 1) (by omega) (h1.trans (map_zero _).symm)
      · exact (hUz j hj0).elim _ _
    have hφ : φ = 0 := by
      have := hU'z (3 - (j - 1)) (by omega) (by omega)
      exact dualCx_ext fun y => by rw [Subsingleton.elim y 0, map_zero, map_zero]
    refine ⟨0, ?_⟩
    rw [map_zero, hu, hx, hφ]
    rfl
  · 
    have hu : u = 0 := (hUz j (by omega)).elim _ _
    rw [hu, map_zero, zero_sub, neg_eq_zero] at h1
    obtain ⟨u', hu'⟩ := hU0 i (j - 1) (by omega) (l - 1) (by omega) (by omega) (-x)
      (by rw [map_neg, h1, neg_zero])
    refine ⟨((((u', 0) : coneT (orthNeg iU) i)), 0), ?_⟩
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · exact (hUz j (by omega)).elim _ _
    · change (orthNeg iU).f i (j - 1) (by omega) u' - L.d (i - 1) (j - 1) (by omega) 0 = x
      rw [map_zero, sub_zero, orthNeg_f_apply, hu', neg_neg]
    · have := hU'z (3 - (j - 1)) (by omega) (by omega)
      exact dualCx_ext fun y => by rw [Subsingleton.elim y 0, map_zero, map_zero]
  · 
    have hu : u = 0 := (hUz j (by omega)).elim _ _
    have hf : ∀ y, L'.d (3 - (l - 1)) (3 - (j - 1)) (by omega) y = 0 →
        trv (P.P (j - 1) (3 - (l - 1)) 2 (by omega) x y) = 0 := by
      intro y hy
      obtain ⟨y₁, rfl⟩ := hU'1 (3 - (l - 1)) (3 - (j - 1)) (by omega) (by omega) y hy
      have h := h2 y₁
      rw [hu, LinearMap.map_zero₂, add_zero] at h
      have : Subsingleton (U'.X (3 - (j - 1))) := hU'z _ (by omega) (by omega)
      rw [h, Subsingleton.elim (U'.d (3 - (l - 1)) (3 - (j - 1)) (by omega) y₁) 0, map_zero,
        smul_zero]
    obtain ⟨z₀, hz₀⟩ := dual_factor_of_ker (L'.d (3 - (l - 1)) (3 - (j - 1)) (by omega))
      (trv ∘ₗ P.P (j - 1) (3 - (l - 1)) 2 (by omega) x) (fun y hy => hf y hy)
    refine trunc01_finish iU iU' P J trv htrv htrv2 hacyc hUz i j l hij hjl (by omega) u x φ hc
      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.sgn (j - 2) • z₀) (fun y => ?_) (fun y => ?_)
    · have : Subsingleton (U'.X (3 - (j - 1))) := hU'z _ (by omega) (by omega)
      rw [Subsingleton.elim y 0]
      simp
    · rw [LinearMap.smul_apply, smul_smul, sgn_mul_self, one_smul, hz₀]
      rfl
  · 
    have hu : u = 0 := (hUz j (by omega)).elim _ _
    obtain ⟨z, hz⟩ := dual_extend_of_injective (iU'.f (3 - (j - 1)) (3 - (j - 1)) rfl) (hU'inj _)
      (asDual φ)
    refine trunc01_finish iU iU' P J trv htrv htrv2 hacyc hUz i j l hij hjl (by omega) u x φ hc z hz
      (fun y => ?_)
    obtain ⟨y₀, rfl⟩ : ∃ y₀, iU'.f (3 - (l - 1)) (3 - (l - 1)) rfl y₀ = y := by
      by_cases h3 : j = 3
      · exact hU'0 _ (by omega) y
      · have := hL'neg (3 - (l - 1)) (by omega)
        exact ⟨0, Subsingleton.elim _ _⟩
    have h := h2 y₀
    rw [hu, LinearMap.map_zero₂, add_zero] at h
    rw [h, ← iU'.comm (3 - (l - 1)) (3 - (j - 1)) (3 - (l - 1)) (3 - (j - 1)) rfl (by omega)
      (by omega) rfl y₀, hz, show j - 2 = j - 1 - 1 by ring, sgn_pred, neg_smul, neg_smul]
    rw [neg_neg, sgn_pred (j - 1), sgn_pred j, neg_neg]

end Trunc01

section Shape

variable {k : Type} [Field k] {ι : Type} [DecidableEq ι]
  {Gv : ι → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)]
  {Mv : ι → Type} [∀ v, AddCommGroup (Mv v)] [∀ v, Module k (Mv v)]
  [∀ v, DistribMulAction (Gv v) (Mv v)] [∀ v, SMulCommClass (Gv v) k (Mv v)]
  [∀ v, TopologicalSpace (Mv v)] [∀ v, ContinuousAdd (Mv v)]
  [∀ v, ContinuousConstSMul k (Mv v)] [∀ v, ContinuousSMul (Gv v) (Mv v)]

theorem natCx_subsingleton_neg (Kc : CochainComplex (ModuleCat.{0} k) ℕ) (n : ℤ) (hn : n < 0) :
    Subsingleton ((natCx Kc).X n) := by
  rcases n with n | n
  · exact absurd hn (not_lt.mpr (Int.natCast_nonneg n))
  · exact (inferInstance : Subsingleton PUnit)

theorem subsingleton_of_eq_bot {V : Type} [AddCommGroup V] [Module k V] (p : Submodule k V)
    (h : p = ⊥) : Subsingleton p := by
  subst h
  infer_instance

theorem strRelK_truncShape01 (q : ι) (old : ∀ v, SubFam (locCxK k Gv Mv v)) :
    TruncShape01 (ghomComp (SubFam.inclLe (switch_hsrK q old q)) (switchRelK k Gv Mv q old q).incl)
      (switchRelK k Gv Mv q old q).incl where
  hLneg n hn := natCx_subsingleton_neg _ n hn
  hL'neg n hn := natCx_subsingleton_neg _ n hn
  hUz n hn := by
    change Subsingleton ↥((switchStrK k Gv Mv q old q).S n)
    rw [switchStr_qK]
    rcases n with (_ | _ | n) | n
    · exact absurd rfl hn
    · exact subsingleton_of_eq_bot _ rfl
    · exact subsingleton_of_eq_bot _ rfl
    · exact subsingleton_of_eq_bot _ rfl
  hU'z n hn hn1 := by
    change Subsingleton ↥((switchRelK k Gv Mv q old q).S n)
    rw [switchRel_qK]
    rcases n with (_ | _ | n) | n
    · exact absurd rfl hn
    · exact absurd rfl hn1
    · exact subsingleton_of_eq_bot _ rfl
    · exact subsingleton_of_eq_bot _ rfl
  hUinj n m h := by
    subst h
    intro a b hab
    exact Subtype.ext hab
  hU0 n m h m' h' hn x hx := by
    subst h hn h'
    have hmem : x ∈ (switchStrK k Gv Mv q old q).S 0 := by
      rw [switchStr_qK]
      exact hx
    exact ⟨⟨x, hmem⟩, rfl⟩
  hU'inj n a b hab := Subtype.ext hab
  hU'0 n hn x := by
    subst hn
    have hmem : x ∈ (switchRelK k Gv Mv q old q).S 0 := by
      rw [switchRel_qK]
      exact (Submodule.mem_top : x ∈ (⊤ : Submodule k ((locCxK k Gv Mv q).X 0)))
    exact ⟨⟨x, hmem⟩, rfl⟩
  hU'1 n m h hn y hy := by
    subst hn h
    have hmem : y ∈ (switchRelK k Gv Mv q old q).S 1 := by
      rw [switchRel_qK]
      exact hy
    exact ⟨⟨y, hmem⟩, rfl⟩

end Shape

section RingTruncations

variable {R : Type} [CommRing R]

/-- A subcomplex over a commutative coefficient ring. -/
structure LocalSubcomplex (C : GCx R) where
  S : ∀ n, Submodule R (C.X n)
  hd : ∀ i j (h : i + 1 = j), S i ≤ (S j).comap (C.d i j h)

/-- The complex of a local subcomplex. -/
def LocalSubcomplex.cx {C : GCx R} (A : LocalSubcomplex C) : GCx R where
  X n := ModuleCat.of R (A.S n)
  d i j h := ((C.d i j h).domRestrict (A.S i)).codRestrict (A.S j) fun x => A.hd i j h x.2
  d_d i j l hij hjl x := Subtype.ext (C.d_d i j l hij hjl x.1)

/-- The inclusion into the actual local complex. -/
def LocalSubcomplex.incl {C : GCx R} (A : LocalSubcomplex C) : GHom A.cx C where
  f i j h := by subst h; exact (A.S i).subtype
  comm i i₁ j j₁ hij h₁ h₂ hj x := by subst hij hj; rfl

/-- The strict derivative condition is the actual zero-cocycles in degree zero. -/
def strictTruncation (C : GCx R) : LocalSubcomplex C where
  S n := if n = 0 then LinearMap.ker (C.d n (n + 1) rfl) else ⊥
  hd i j hij x hx := by
    subst hij
    change C.d i (i + 1) rfl x ∈
      (if i + 1 = 0 then LinearMap.ker (C.d (i + 1) (i + 1 + 1) rfl) else ⊥)
    by_cases hi : i = 0
    · subst hi
      change x ∈ LinearMap.ker (C.d 0 1 rfl) at hx
      rw [LinearMap.mem_ker] at hx
      change C.d 0 1 rfl x ∈ (⊥ : Submodule R (C.X 1))
      rw [hx]
      exact Submodule.zero_mem _
    · change x ∈ (if i = 0 then LinearMap.ker (C.d i (i + 1) rfl) else ⊥) at hx
      rw [ite_eq_right hi, Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact Submodule.zero_mem _

/-- The relaxed derivative condition is the actual truncation through degree one. -/
def relaxedTruncation (C : GCx R) : LocalSubcomplex C where
  S n := if n = 0 then ⊤ else if n = 1 then LinearMap.ker (C.d n (n + 1) rfl) else ⊥
  hd i j hij x hx := by
    subst hij
    change C.d i (i + 1) rfl x ∈
      (if i + 1 = 0 then ⊤ else if i + 1 = 1 then LinearMap.ker (C.d (i + 1) (i + 1 + 1) rfl) else ⊥)
    by_cases hi : i = 0
    · subst hi
      change C.d 0 1 rfl x ∈ LinearMap.ker (C.d 1 2 rfl)
      exact C.d_d 0 1 2 rfl rfl x
    · by_cases hi1 : i = 1
      · subst hi1
        change x ∈ LinearMap.ker (C.d 1 2 rfl) at hx
        rw [LinearMap.mem_ker] at hx
        change C.d 1 2 rfl x ∈ (⊥ : Submodule R (C.X 2))
        rw [hx]
        exact Submodule.zero_mem _
      · change x ∈ (if i = 0 then ⊤ else if i = 1 then LinearMap.ker (C.d i (i + 1) rfl) else ⊥) at hx
        rw [ite_eq_right hi, ite_eq_right hi1, Submodule.mem_bot] at hx
        rw [hx, map_zero]
        exact Submodule.zero_mem _

/-- These are genuine truncation maps, with all local degree-zero cohomology retained. -/
theorem ringTruncation_shape (C C' : GCx R)
    (hC : ∀ n, n < 0 → Subsingleton (C.X n))
    (hC' : ∀ n, n < 0 → Subsingleton (C'.X n)) :
    TruncShape01 (strictTruncation C).incl (relaxedTruncation C').incl where
  hLneg := hC
  hL'neg := hC'
  hUz n hn := by
    change Subsingleton ↥((strictTruncation C).S n)
    simp only [strictTruncation, ite_eq_right hn]
    infer_instance
  hU'z n hn hn1 := by
    change Subsingleton ↥((relaxedTruncation C').S n)
    simp only [relaxedTruncation, ite_eq_right hn, ite_eq_right hn1]
    infer_instance
  hUinj n m h := by
    subst h
    intro a b hab
    exact Subtype.ext hab
  hU0 n m h m' h' hn x hx := by
    subst h hn h'
    exact ⟨⟨x, hx⟩, rfl⟩
  hU'inj n a b hab := Subtype.ext hab
  hU'0 n hn x := by
    subst hn
    exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩
  hU'1 n m h hn y hy := by
    subst hn h
    exact ⟨⟨y, hy⟩, rfl⟩

/-- The strict and relaxed derivative conditions are complementary over every
self-injective commutative ring, for the full local-duality cup map. -/
theorem strict_relaxed_local_complement [Module.Injective R R]
    {C C' E : GCx R} (P : GPair C C' E)
    (J : LocalTruncIsotropy (strictTruncation C).incl (relaxedTruncation C').incl P)
    (trv : E.X 2 →ₗ[R] R) (htrv : ∀ z, trv (E.d 1 2 rfl z) = 0)
    (hC : ∀ n, n < 0 → Subsingleton (C.X n))
    (hC' : ∀ n, n < 0 → Subsingleton (C'.X n))
    (hLD : QuasiIso (GHom.toCC (adjHom P 2 trv htrv))) :
    QuasiIso (GHom.toCC (orthLocalMap (strictTruncation C).incl
      (relaxedTruncation C').incl P J trv htrv)) :=
  trunc01_quasiIso _ _ P J trv htrv htrv (coneCx_acyclic_of_quasiIso _ hLD)
    (ringTruncation_shape C C' hC hC')

end RingTruncations

section GaloisTruncations

open ZInQ.Manuscript.RC.CoefModules

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {R : Type} [CommRing R] {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]

/-- The strict derivative condition on the actual local cochains. -/
def derivativeStrictAt (v : Places K S) : CondAt K S R M v :=
  ⟨(strictTruncation (locAt K S R M v)).cx, (strictTruncation (locAt K S R M v)).incl⟩

/-- The relaxed derivative condition on the actual local cochains. -/
def derivativeRelaxedAt (v : Places K S) : CondAt K S R M v :=
  ⟨(relaxedTruncation (locAt K S R M v)).cx, (relaxedTruncation (locAt K S R M v)).incl⟩

variable (β : M →ₗ[R] M' →ₗ[R] T)
  (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

/-- Derived orthogonality of the two actual derivative truncations. -/
theorem derivativeAt_local_complement [Module.Injective R R] (v : Places K S)
    (trv : (locAt K S R T v).X 2 →ₗ[R] R)
    (htrv : ∀ z, trv ((locAt K S R T v).d 1 2 rfl z) = 0)
    (J : LocalTruncIsotropy (derivativeStrictAt (M := M) v).i
      (derivativeRelaxedAt (M := M') v).i (orthGaloisPair K β hβ v))
    (hLD : QuasiIso (GHom.toCC (adjHom (orthGaloisPair K β hβ v) 2 trv htrv))) :
    QuasiIso (GHom.toCC (orthLocalMap (derivativeStrictAt (M := M) v).i
      (derivativeRelaxedAt (M := M') v).i (orthGaloisPair K β hβ v) J trv htrv)) :=
  strict_relaxed_local_complement (orthGaloisPair K β hβ v) J trv htrv
    (orth_locAt_neg (R := R) (M := M) v) (orth_locAt_neg (R := R) (M := M') v) hLD

open scoped Classical in
/-- Retain the old condition outside the specified derivative places. -/
def strictOverrideAt (Q : Finset (Places K S))
    (old : ∀ v : Places K S, CondAt K S R M v) (v : Places K S) : CondAt K S R M v :=
  if v ∈ Q then derivativeStrictAt v else old v

open scoped Classical in
/-- Retain the dual old condition outside the specified derivative places. -/
def relaxedOverrideAt (Q : Finset (Places K S))
    (old : ∀ v : Places K S, CondAt K S R M v) (v : Places K S) : CondAt K S R M v :=
  if v ∈ Q then derivativeRelaxedAt v else old v

/-- Placewise assembly for a derivative override, with the old comparisons
supplied by their established local-duality theorem. -/
theorem derivativeOverride_horth [Module.Injective R R] [Fintype (Places K S)]
    (Q : Finset (Places K S))
    (oldA : ∀ v : Places K S, CondAt K S R M v)
    (oldB : ∀ v : Places K S, CondAt K S R M' v)
    (I : GaloisTruncIsotropyData K S R β hβ
      (ofCondAt K S R M (strictOverrideAt Q oldA))
      (ofCondAt K S R M' (relaxedOverrideAt Q oldB)))
    (trv : ∀ v : Places K S, (locAt K S R T v).X 2 →ₗ[R] R)
    (htrv : ∀ v z, trv v ((locAt K S R T v).d 1 2 rfl z) = 0)
    (hOld : ∀ v (J : LocalTruncIsotropy (oldA v).i (oldB v).i (orthGaloisPair K β hβ v)),
      QuasiIso (GHom.toCC (orthLocalMap (oldA v).i (oldB v).i (orthGaloisPair K β hβ v)
        J (trv v) (htrv v))))
    (hLD : ∀ v, v ∈ Q → QuasiIso (GHom.toCC (adjHom (orthGaloisPair K β hβ v)
      2 (trv v) (htrv v))))
    (tr : (galoisCompactTT K S R β hβ
      (ofCondAt K S R M (strictOverrideAt Q oldA))
      (ofCondAt K S R M' (relaxedOverrideAt Q oldB)) I).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((galoisCompactTT K S R β hβ
      (ofCondAt K S R M (strictOverrideAt Q oldA))
      (ofCondAt K S R M' (relaxedOverrideAt Q oldB)) I).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1),
      tr ((0 : (globalCx R (GKS K S) T).X 3),
        (truncSub (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) T) (3 - 1)).mkQ z) = ∑ v, trv v (z v)) :
    OrthogonalComplementsT K β hβ
      (ofCondAt K S R M (strictOverrideAt Q oldA))
      (ofCondAt K S R M' (relaxedOverrideAt Q oldB)) I tr htr := by
  classical
  apply orthogonalComplementsT_of_places K β hβ _ _ I trv htrv tr htr hsum
  intro v
  by_cases hv : v ∈ Q
  · exact actLPerf_congr β hβ
      (show strictOverrideAt Q oldA v = derivativeStrictAt v from ite_eq_left hv)
      (show relaxedOverrideAt Q oldB v = derivativeRelaxedAt v from ite_eq_left hv)
      (trv v) (htrv v)
      (fun J => derivativeAt_local_complement β hβ v (trv v) (htrv v) J (hLD v hv)) (I.toLocal v)
  · exact actLPerf_congr β hβ
      (show strictOverrideAt Q oldA v = oldA v from ite_eq_right hv)
      (show relaxedOverrideAt Q oldB v = oldB v from ite_eq_right hv)
      (trv v) (htrv v) (hOld v) (I.toLocal v)

end GaloisTruncations

section ActualStages

open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.Duality (MilneLocalTateDualityKummerCharZero)

variable {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S₀ W (2 ^ i)) (P : Set (HeightOneSpectrum (𝓞 K)))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α] (hμ : HasRootsOfUnity K S₀ (2 ^ i))
  (hα : ∀ v ∈ P, IsLocallyQuadAt i α (quadChar s hs hs0) v)

/-- The actual old conditions, with strict derivative truncations inserted. -/
def stageStrictConditions (Q : Finset (Places K S)) :
    GaloisLocalConditions K S (Acoef i) (MinS hS W i α) :=
  ofCondAt K S (Acoef i) (MinS hS W i α)
    (strictOverrideAt Q (actLCondA hS W i s hs hs0 hFull P α hα))

/-- The actual dual old conditions, with relaxed derivative truncations inserted. -/
def stageRelaxedConditions (Q : Finset (Places K S)) :
    GaloisLocalConditions K S (Acoef i) (MinS hS W i (charInv α)) :=
  ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
    (relaxedOverrideAt Q (actLCondB hS W i s hs hs0 hFull P α hα))

/-- Orthogonality for the actual old stage conditions including derivative
places. The non-derivative comparisons are RC29's theorem, not hypotheses.
The derivative comparisons follow from the full local-duality print and the
proved truncation-cone computation. -/
theorem orthogonalComplementsT_actual_derivatives [Fintype (Places K S)]
    (Q : Finset (Places K S))
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K) (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (I : GaloisTruncIsotropyData K S (Acoef i) (actLBeta hS W i α hμ)
      (actLBeta_smul hS W i α hμ)
      (stageStrictConditions hS W i s hs hs0 hFull P α hα Q)
      (stageRelaxedConditions hS W i s hs hs0 hFull P α hα Q))
    (trv : ∀ v : Places K S, (locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ)) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ v z, trv v ((locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ)) v).d 1 2 rfl z) = 0)
    (htrv2 : ∀ v, InducesIsoH2 (trv v))
    (tr : (galoisCompactTT K S (Acoef i) (actLBeta hS W i α hμ)
      (actLBeta_smul hS W i α hμ)
      (stageStrictConditions hS W i s hs hs0 hFull P α hα Q)
      (stageRelaxedConditions hS W i s hs hs0 hFull P α hα Q) I).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i) (actLBeta hS W i α hμ)
      (actLBeta_smul hS W i α hμ)
      (stageStrictConditions hS W i s hs hs0 hFull P α hα Q)
      (stageRelaxedConditions hS W i s hs hs0 hFull P α hα Q) I).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ))).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (InflMod hS (Tate1 (Acoef i) hμ))).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ))) (3 - 1)).mkQ z) = ∑ v, trv v (z v)) :
    OrthogonalComplementsT K (actLBeta hS W i α hμ) (actLBeta_smul hS W i α hμ)
      (stageStrictConditions hS W i s hs hs0 hFull P α hα Q)
      (stageRelaxedConditions hS W i s hs hs0 hFull P α hα Q) I tr htr := by
  have := acoef_selfInjective i
  have : Finite (MinS hS W i α) := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  have : Finite (MinS hS W i (charInv α)) := inferInstanceAs (Finite (Mcoef K S₀ W i (charInv α)))
  apply derivativeOverride_horth (actLBeta hS W i α hμ) (actLBeta_smul hS W i α hμ) Q
    (actLCondA hS W i s hs hs0 hFull P α hα) (actLCondB hS W i s hs hs0 hFull P α hα)
    I trv htrv
    (fun v J => actLPerf hS W i s hs hs0 hFull P α hμ hα trv htrv hM h524 h756 hK hSfin hS₀fin
      h2₀ htrv2 v J) ?_ tr htr hsum
  intro v _
  exact h524 S 2 (Acoef i) (nekovarFiniteSetting_acoef K hK S hSfin (fun v hv => hS (h2₀ v hv)) i)
    (MinS hS W i α) (MinS hS W i (charInv α)) (InflMod hS (Tate1 (Acoef i) hμ))
    (actLBeta hS W i α hμ) (actLBeta_smul hS W i α hμ)
    (weilPairingM_bijective (S := S₀) W hμ (Acoef i) α hFull)
    (weilPairingM_flip_bijective (S := S₀) W hμ (Acoef i) α hFull)
    (cycloInfl_isCyclotomicTwist_tate1 hS i hμ) v (trv v) (htrv v) (htrv2 v)

end ActualStages

section ActualSelmerStages

open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.Duality (MilneLocalTateDualityKummerCharZero)

variable {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S₀ W (2 ^ i)) (P : Set (HeightOneSpectrum (𝓞 K)))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α] (hμ : HasRootsOfUnity K S₀ (2 ^ i))
  (hα : ∀ v ∈ P, IsLocallyQuadAt i α (quadChar s hs hs0) v)

/-- Finite Selmer duality with the actual old conditions and the derivative
truncation pair. The local orthogonality hypothesis is supplied, not assumed. -/
theorem selmerDuality_actual_derivatives [Fintype (Places K S)]
    (Q : Finset (Places K S))
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K)
    (h543 : NekovarProp543T K) (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (I : GaloisTruncIsotropyData K S (Acoef i) (actLBeta hS W i α hμ)
      (actLBeta_smul hS W i α hμ)
      (stageStrictConditions hS W i s hs hs0 hFull P α hα Q)
      (stageRelaxedConditions hS W i s hs hs0 hFull P α hα Q))
    (trv : ∀ v : Places K S, (locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ)) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ v z, trv v ((locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ)) v).d 1 2 rfl z) = 0)
    (htrv2 : ∀ v, InducesIsoH2 (trv v))
    (tr : (galoisCompactTT K S (Acoef i) (actLBeta hS W i α hμ)
      (actLBeta_smul hS W i α hμ)
      (stageStrictConditions hS W i s hs hs0 hFull P α hα Q)
      (stageRelaxedConditions hS W i s hs hs0 hFull P α hα Q) I).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i) (actLBeta hS W i α hμ)
      (actLBeta_smul hS W i α hμ)
      (stageStrictConditions hS W i s hs hs0 hFull P α hα Q)
      (stageRelaxedConditions hS W i s hs hs0 hFull P α hα Q) I).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ))).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (InflMod hS (Tate1 (Acoef i) hμ))).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ))) (3 - 1)).mkQ z) = ∑ v, trv v (z v))
    (htr3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (selmerDualityMap
      (galoisPairDataT K S (Acoef i) (actLBeta hS W i α hμ) (actLBeta_smul hS W i α hμ)
        (stageStrictConditions hS W i s hs hs0 hFull P α hα Q)
        (stageRelaxedConditions hS W i s hs hs0 hFull P α hα Q) I) tr htr)) := by
  have : Finite (MinS hS W i α) := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  have : Finite (MinS hS W i (charInv α)) := inferInstanceAs (Finite (Mcoef K S₀ W i (charInv α)))
  exact genuineSelmerDualityT K (actLBeta hS W i α hμ) (actLBeta_smul hS W i α hμ)
    (stageStrictConditions hS W i s hs hs0 hFull P α hα Q)
    (stageRelaxedConditions hS W i s hs hs0 hFull P α hα Q) I tr htr h543 2
    (nekovarFiniteSetting_acoef K hK S hSfin (fun v hv => hS (h2₀ v hv)) i)
    (weilPairingM_bijective (S := S₀) W hμ (Acoef i) α hFull)
    (weilPairingM_flip_bijective (S := S₀) W hμ (Acoef i) α hFull)
    (cycloInfl_isCyclotomicTwist_tate1 hS i hμ) htr3
    (orthogonalComplementsT_actual_derivatives hS W i s hs hs0 hFull P α hμ hα Q
      hM h524 h756 hK hSfin hS₀fin h2₀ I trv htrv htrv2 tr htr hsum)

end ActualSelmerStages

section DirectStage

open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α] (hμ : HasRootsOfUnity K S (2 ^ i))

/-- The derivative complement on the exact coefficient modules of the stage
Selmer-duality theorem. No change of support or coefficient representation is
used in this local statement. -/
theorem stageDerivative_local_complement (h524 : NekovarProp524 K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hFull : FullTorsion K S W (2 ^ i)) (v : Places K S)
    (trv : (locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ z, trv ((locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).d 1 2 rfl z) = 0)
    (htrv2 : InducesIsoH2 trv)
    (J : LocalTruncIsotropy
      (derivativeStrictAt (M := Mcoef K S W i α) v).i
      (derivativeRelaxedAt (M := Mcoef K S W i (charInv α)) v).i
      (orthGaloisPair K (weilPairingData W i α hμ) (weilPairingM_smul W hμ (Acoef i) α) v)) :
    QuasiIso (GHom.toCC (orthLocalMap
      (derivativeStrictAt (M := Mcoef K S W i α) v).i
      (derivativeRelaxedAt (M := Mcoef K S W i (charInv α)) v).i
      (orthGaloisPair K (weilPairingData W i α hμ) (weilPairingM_smul W hμ (Acoef i) α) v)
      J trv htrv)) := by
  have := acoef_selfInjective i
  apply derivativeAt_local_complement (weilPairingData W i α hμ)
    (weilPairingM_smul W hμ (Acoef i) α) v trv htrv J
  exact h524 S 2 (Acoef i) (nekovarFiniteSetting_acoef K hK S hSfin h2 i)
    (Mcoef K S W i α) (Mcoef K S W i (charInv α)) (Tate1 (Acoef i) hμ)
    (weilPairingData W i α hμ) (weilPairingM_smul W hμ (Acoef i) α)
    (weilPairingM_bijective W hμ (Acoef i) α hFull)
    (weilPairingM_flip_bijective W hμ (Acoef i) α hFull)
    (isCyclotomicTwist_tate1 (Acoef i) hμ) v trv htrv htrv2

end DirectStage

end ZInQ.Contrib.RC53Assist.OldOrthogonality.Truncations



/-!
# Coefficient modules under enlargement of the Galois support

The inclusion of the fields defining the finite torsion gives the canonical
comparison from the inflated coefficient module to the coefficient module
formed over the larger support. It is bijective when the old support already
contains the full torsion. The comparison is linear over the actual coefficient
algebra and equivariant for the actual Galois action.
-/

set_option maxHeartbeats 600000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.OldOrthogonality.SupportCoefficients

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.Duality (baseChangeAct baseChangeAct_tmul)
open scoped TensorProduct

section PointMaps

variable {F L : Type} [Field F] [Field L] [DecidableEq L] [Algebra F L]

/-- Compatibility of point maps with inclusions of intermediate fields. -/
theorem pointFields_comp (V : WeierstrassCurve F) (A B : IntermediateField F L)
    [DecidableEq A] [DecidableEq B] (hAB : A ≤ B) (p : (V.baseChange A).toAffine.Point) :
    Affine.Point.map (W' := V) B.val
        (Affine.Point.map (W' := V) (IntermediateField.inclusion hAB) p) =
      Affine.Point.map (W' := V) A.val p := by
  have hi : B.val.comp (IntermediateField.inclusion hAB) = A.val :=
    AlgHom.ext (IntermediateField.coe_inclusion hAB)
  rw [Affine.Point.map_map, hi]

end PointMaps

variable {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic]

omit [NumberField K] [W.IsElliptic] in
set_option maxHeartbeats 800000 in
/-- Point maps along support inclusions agree in the algebraic closure. -/
theorem pointSupport_comp (p : (W.baseChange (KS K S₀)).toAffine.Point) :
    Affine.Point.map (W' := W) (inclS K S)
        (Affine.Point.map (W' := W) (cycloInflIncl hS) p) =
      Affine.Point.map (W' := W) (inclS K S₀) p :=
  pointFields_comp W (unramifiedOutside K S₀) (unramifiedOutside K S)
    (unramifiedOutside_mono K hS) p

section Torsion

variable (n : ℕ) [NeZero n]

/-- The torsion point map along the canonical inclusion of the fields. -/
def torsionSupportMap : TorsS K S₀ W (n : ℤ) →+ TorsS K S W (n : ℤ) where
  toFun t := ⟨Affine.Point.map (W' := W) (cycloInflIncl hS) t.1, by
    have ht : (n : ℤ) • t.1 = 0 := (Submodule.mem_torsionBy_iff _ _).mp t.2
    change (n : ℤ) • Affine.Point.map (W' := W) (cycloInflIncl hS) t.1 = 0
    rw [← map_zsmul, ht, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' t u := Subtype.ext (map_add _ _ _)

theorem torsionSupportMap_coe (t : TorsS K S₀ W (n : ℤ)) :
    ((torsionSupportMap hS W n t : TorsS K S W (n : ℤ)) : (W.baseChange (KS K S)).toAffine.Point) =
      Affine.Point.map (W' := W) (cycloInflIncl hS) t.1 := rfl

/-- The point map preserves the inclusion in the algebraic closure. -/
theorem inclTors_torsionSupportMap (t : TorsS K S₀ W (n : ℤ)) :
    inclTors (S := S) W n (torsionSupportMap hS W n t) = inclTors (S := S₀) W n t := by
  apply Subtype.ext
  change Affine.Point.map (W' := W) (inclS K S)
      (Affine.Point.map (W' := W) (cycloInflIncl hS) t.1) =
    Affine.Point.map (W' := W) (inclS K S₀) t.1
  exact pointSupport_comp hS W t.1

theorem torsionSupportMap_injective : Function.Injective (torsionSupportMap hS W n) := by
  intro t u htu
  apply Subtype.ext
  exact Affine.Point.map_injective (cycloInflIncl hS) (congrArg Subtype.val htu)

include hS in
/-- Enlargement of the support retains the full torsion. -/
theorem fullTorsion_afterSupport (hFull : FullTorsion K S₀ W n) : FullTorsion K S W n := by
  have : Finite (TorsS K S₀ W (n : ℤ)) := finite_torsS (by exact_mod_cast NeZero.ne n)
  have : Finite (TorsS K S W (n : ℤ)) := finite_torsS (by exact_mod_cast NeZero.ne n)
  have hlo : n ^ 2 ≤ Nat.card (TorsS K S W (n : ℤ)) := by
    rw [← hFull]
    exact Nat.card_le_card_of_injective _ (torsionSupportMap_injective hS W n)
  have hhi : Nat.card (TorsS K S W (n : ℤ)) ≤ n ^ 2 := by
    rw [← natCard_torsBar W n]
    exact Nat.card_le_card_of_injective _ (inclTors_injective (S := S) W n)
  exact le_antisymm hhi hlo

/-- The canonical torsion comparison is an additive equivalence. -/
def torsionSupportEquiv (hFull : FullTorsion K S₀ W n) :
    TorsS K S₀ W (n : ℤ) ≃+ TorsS K S W (n : ℤ) := by
  have : Finite (TorsS K S W (n : ℤ)) := finite_torsS (by exact_mod_cast NeZero.ne n)
  exact AddEquiv.ofBijective (torsionSupportMap hS W n)
    ((torsionSupportMap_injective hS W n).bijective_of_nat_card_le (by
      rw [hFull, fullTorsion_afterSupport hS W n hFull]))

/-- Equivariance uses restriction of the Galois action, not a chosen lift. -/
theorem torsionSupportMap_smul (g : GKS K S) (t : TorsS K S₀ W (n : ℤ)) :
    torsionSupportMap hS W n (inflMap K hS g • t) = g • torsionSupportMap hS W n t := by
  have hc : (cycloInflIncl hS).comp (galS K S₀ (inflMap K hS g)).toAlgHom =
      (galS K S g).toAlgHom.comp (cycloInflIncl hS) :=
    AlgHom.ext fun x => (cycloInfl_galS_incl hS g x).symm
  apply Subtype.ext
  rw [torsionSupportMap_coe, coe_smul_torsS, coe_smul_torsS,
    torsionSupportMap_coe, Affine.Point.map_map, Affine.Point.map_map, hc]

end Torsion

section Coefficients

variable (i : ℕ) (α : GKS K S₀ →* (Acoef i)ˣ)

/-- The same coefficient character on the enlarged support. -/
def characterAfterSupport : GKS K S →* (Acoef i)ˣ :=
  α.comp (inflMap K hS).toMonoidHom

@[simp]
theorem characterAfterSupport_apply (g : GKS K S) :
    characterAfterSupport hS i α g = α (inflMap K hS g) := rfl

instance characterAfterSupport_isOpenKer [IsOpenKer α] :
    IsOpenKer (characterAfterSupport hS i α) := by
  refine ⟨?_⟩
  have h := (IsOpenKer.isOpen_ker (α := α)).preimage (inflMap K hS).continuous
  change IsOpen ((inflMap K hS) ⁻¹' (α.ker : Set (GKS K S₀))) at h
  exact h

/-- Extension of the torsion point map to the actual finite coefficient algebra. -/
def coefficientSupportMap : MinS hS W i α →ₗ[Acoef i]
    Mcoef K S W i (characterAfterSupport hS i α) :=
  (torsionSupportMap hS W (2 ^ i)).toIntLinearMap.baseChange (Acoef i)

theorem coefficientSupportMap_tmul (a : Acoef i)
    (t : TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) :
    coefficientSupportMap hS W i α (CoefMod.equiv (Acoef i) α _ (a ⊗ₜ t)) =
      CoefMod.equiv (Acoef i) (characterAfterSupport hS i α) _
        (a ⊗ₜ torsionSupportMap hS W (2 ^ i) t) :=
  LinearMap.baseChange_tmul _ _ _

/-- The actual stage coefficient comparison is a linear equivalence. -/
def coefficientSupportEquiv (hFull : FullTorsion K S₀ W (2 ^ i)) :
    MinS hS W i α ≃ₗ[Acoef i] Mcoef K S W i (characterAfterSupport hS i α) :=
  (CoefMod.equiv (Acoef i) α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))).symm.trans
    ((LinearEquiv.baseChange ℤ (Acoef i) _ _
      (torsionSupportEquiv hS W (2 ^ i) hFull).toIntLinearEquiv).trans
      (CoefMod.equiv (Acoef i) (characterAfterSupport hS i α)
        (TorsS K S W ((2 ^ i : ℕ) : ℤ))))

/-- The linear equivalence is the same actual coefficient map. -/
theorem coefficientSupportEquiv_apply (hFull : FullTorsion K S₀ W (2 ^ i))
    (x : MinS hS W i α) :
    coefficientSupportEquiv hS W i α hFull x = coefficientSupportMap hS W i α x := rfl

/-- The stage coefficient comparison is equivariant for the unchanged character. -/
theorem coefficientSupportMap_smul (g : GKS K S) (z : MinS hS W i α) :
    coefficientSupportMap hS W i α (g • z) = g • coefficientSupportMap hS W i α z := by
  let f : (Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) →ₗ[Acoef i]
      (Acoef i ⊗[ℤ] TorsS K S W ((2 ^ i : ℕ) : ℤ)) :=
    (torsionSupportMap hS W (2 ^ i)).toIntLinearMap.baseChange (Acoef i)
  have hf : ∀ x : Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ),
      f (baseChangeAct (Acoef i) (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) (inflMap K hS g) x) =
        baseChangeAct (Acoef i) (TorsS K S W ((2 ^ i : ℕ) : ℤ)) g (f x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a t =>
      rw [baseChangeAct_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, baseChangeAct_tmul]
      exact congrArg (fun t' => a ⊗ₜ[ℤ] t') (torsionSupportMap_smul hS W (2 ^ i) g t)
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  change f (((α (inflMap K hS g) : (Acoef i)ˣ) : Acoef i) •
      baseChangeAct (Acoef i) (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) (inflMap K hS g)
        (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from z)) =
    ((characterAfterSupport hS i α g : (Acoef i)ˣ) : Acoef i) •
      baseChangeAct (Acoef i) (TorsS K S W ((2 ^ i : ℕ) : ℤ)) g
        (f (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from z))
  rw [map_smul, hf, characterAfterSupport_apply]

end Coefficients

end ZInQ.Contrib.RC53Assist.OldOrthogonality.SupportCoefficients

namespace ZInQ.Contrib.RC53Assist.OldOrthogonality.SupportCoefficients

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps ZInQ.Manuscript.RC.HeegnerAlgebra
open scoped TensorProduct

section RootFrames

variable {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ} [NeZero n]
  (hμ₀ : HasRootsOfUnity K S₀ n) (hμ : HasRootsOfUnity K S n)

/-- The change between the two discrete logarithms of the same roots of unity. -/
def rootLogChange : ZMod n ≃+ ZMod n := (logBar hμ₀).symm.trans (logBar hμ)

theorem rootLogChange_apply (z : ZMod n) :
    rootLogChange hμ₀ hμ z = z * rootLogChange hμ₀ hμ 1 := by
  simpa only [smul_eq_mul, mul_one] using ZMod.map_smul (rootLogChange hμ₀ hμ) z (1 : ZMod n)

theorem rootLogChange_one_isUnit : IsUnit (rootLogChange hμ₀ hμ 1) := by
  obtain ⟨z, hz⟩ := (rootLogChange hμ₀ hμ).surjective 1
  apply IsUnit.of_mul_eq_one z
  rw [mul_comm, ← rootLogChange_apply]
  exact hz

/-- The unit that compares the Weil-pairing normalizations after support change. -/
def supportLogUnit : (ZMod n)ˣ := (rootLogChange_one_isUnit hμ₀ hμ).unit

theorem supportLogUnit_val : (supportLogUnit hμ₀ hμ : ZMod n) = rootLogChange hμ₀ hμ 1 :=
  IsUnit.unit_spec _

/-- The normalization changes by a unit, not by equality of chosen primitive roots. -/
theorem logBar_afterSupport (w : Additive (rootsOfUnity n (AlgebraicClosure K))) :
    logBar hμ w = (supportLogUnit hμ₀ hμ : ZMod n) * logBar hμ₀ w := by
  have h := rootLogChange_apply hμ₀ hμ (logBar hμ₀ w)
  change logBar hμ ((logBar hμ₀).symm (logBar hμ₀ w)) = _ at h
  rw [AddEquiv.symm_apply_apply] at h
  rw [supportLogUnit_val, mul_comm]
  exact h

/-- Restriction of support leaves the actual cyclotomic character unchanged. -/
theorem cycS_afterSupport (hS : S₀ ⊆ S) (g : GKS K S) :
    cycS hμ g = cycS hμ₀ (inflMap K hS g) := by
  apply Units.ext
  apply ZMod.val_injective
  have hnew := cycS_spec hμ g (Classical.choose_spec hμ).pow_eq_one
  have hold := cycloInfl_galS_root hS hμ₀ g
    (((cycS hμ₀ (inflMap K hS g) : (ZMod n)ˣ) : ZMod n).val)
    (fun z hz => cycS_spec hμ₀ (inflMap K hS g) hz) (Classical.choose_spec hμ).pow_eq_one
  exact (Classical.choose_spec hμ).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hnew.symm.trans hold)

variable (A : Type) [CommRing A] [Algebra (ZMod n) A]

/-- The same normalization unit in the actual coefficient algebra. -/
def supportUnit : Aˣ := Units.map (algebraMap (ZMod n) A) (supportLogUnit hμ₀ hμ)

/-- The cyclotomic target comparison retains the local-invariant normalization. -/
def tateSupportEquiv (hS : S₀ ⊆ S) :
    InflMod hS (Tate1 A hμ₀) ≃ₗ[A] Tate1 A hμ where
  toFun z := (supportUnit hμ₀ hμ A : A) * (show A from z)
  invFun z := (((supportUnit hμ₀ hμ A)⁻¹ : Aˣ) : A) * (show A from z)
  left_inv z := by
    change (((supportUnit hμ₀ hμ A)⁻¹ : Aˣ) : A) * ((supportUnit hμ₀ hμ A : A) * (show A from z)) = z
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv z := by
    change (supportUnit hμ₀ hμ A : A) * ((((supportUnit hμ₀ hμ A)⁻¹ : Aˣ) : A) * (show A from z)) = z
    rw [← mul_assoc, Units.mul_inv, one_mul]
  map_add' z w := by
    change (supportUnit hμ₀ hμ A : A) * ((show A from z) + (show A from w)) =
      (supportUnit hμ₀ hμ A : A) * (show A from z) + (supportUnit hμ₀ hμ A : A) * (show A from w)
    exact mul_add _ _ _
  map_smul' r z := by
    change (supportUnit hμ₀ hμ A : A) * (r * (show A from z)) =
      r * ((supportUnit hμ₀ hμ A : A) * (show A from z))
    ring

/-- This target comparison is equivariant for the actual Galois action. -/
theorem tateSupportEquiv_smul (hS : S₀ ⊆ S) (g : GKS K S) (z : InflMod hS (Tate1 A hμ₀)) :
    tateSupportEquiv hμ₀ hμ A hS (g • z) = g • tateSupportEquiv hμ₀ hμ A hS z := by
  change (supportUnit hμ₀ hμ A : A) *
      (algebraMap (ZMod n) A (cycS hμ₀ (inflMap K hS g)) * (show A from z)) =
    algebraMap (ZMod n) A (cycS hμ g) * ((supportUnit hμ₀ hμ A : A) * (show A from z))
  rw [cycS_afterSupport hμ₀ hμ hS g]
  ring

end RootFrames

section WeilFrames

variable {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ) [NeZero n]
  (hμ₀ : HasRootsOfUnity K S₀ n) (hμ : HasRootsOfUnity K S n)

/-- The canonical torsion comparison carries the actual Weil pairing with
its precise normalization unit. -/
theorem weilS_afterSupport (x y : TorsS K S₀ W (n : ℤ)) :
    weilS (S := S) W hμ (torsionSupportMap hS W n x) (torsionSupportMap hS W n y) =
      (supportLogUnit hμ₀ hμ : ZMod n) * weilS (S := S₀) W hμ₀ x y := by
  rw [weilS_apply, weilS_apply, inclTors_torsionSupportMap, inclTors_torsionSupportMap,
    logBar_afterSupport hμ₀ hμ]

variable (A : Type) [CommRing A] [Algebra (ZMod n) A]

/-- Scalar extension preserves this exact comparison of Weil pairings. -/
theorem weilA_afterSupport (x y : A ⊗[ℤ] TorsS K S₀ W (n : ℤ)) :
    weilA (S := S) W hμ A
      ((torsionSupportMap hS W n).toIntLinearMap.baseChange A x)
      ((torsionSupportMap hS W n).toIntLinearMap.baseChange A y) =
        (supportUnit hμ₀ hμ A : A) * weilA (S := S₀) W hμ₀ A x y := by
  induction x using TensorProduct.inductionOn with
  | tmul a t =>
    induction y using TensorProduct.inductionOn with
    | tmul b u =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, weilA_tmul, weilA_tmul]
      change a * b * algebraMap (ZMod n) A
          (weilS W hμ (torsionSupportMap hS W n t) (torsionSupportMap hS W n u)) =
        (supportUnit hμ₀ hμ A : A) * (a * b * algebraMap (ZMod n) A (weilS W hμ₀ t u))
      rw [weilS_afterSupport, map_mul]
      change a * b * (algebraMap (ZMod n) A (supportLogUnit hμ₀ hμ) *
          algebraMap (ZMod n) A (weilS W hμ₀ t u)) =
        algebraMap (ZMod n) A (supportLogUnit hμ₀ hμ) * (a * b * algebraMap (ZMod n) A (weilS W hμ₀ t u))
      ring
    | add y z hy hz =>
      rw [map_add, map_add, map_add, mul_add, hy, hz]
  | add x z hx hz =>
    rw [map_add, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, mul_add, hx, hz]

end WeilFrames

section StageFrames

variable {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  (α : GKS K S₀ →* (Acoef i)ˣ) (hFull : FullTorsion K S₀ W (2 ^ i))
  (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i)) (hμ : HasRootsOfUnity K S (2 ^ i))

/-- Inverse characters commute with the actual restriction of support. -/
theorem characterAfterSupport_charInv :
    characterAfterSupport hS i (charInv α) = charInv (characterAfterSupport hS i α) := by
  ext g
  rfl

/-- Equivariance of the exact coefficient equivalence. -/
theorem coefficientSupportEquiv_smul (g : GKS K S) (x : MinS hS W i α) :
    coefficientSupportEquiv hS W i α hFull (g • x) =
      g • coefficientSupportEquiv hS W i α hFull x := by
  rw [coefficientSupportEquiv_apply, coefficientSupportEquiv_apply]
  exact coefficientSupportMap_smul hS W i α g x

/-- The same coefficient equivalence on the actual dual stage module. -/
def dualCoefficientSupportEquiv : MinS hS W i (charInv α) ≃ₗ[Acoef i]
    Mcoef K S W i (charInv (characterAfterSupport hS i α)) :=
  coefficientSupportEquiv hS W i (charInv α) hFull

/-- Equivariance is retained in the dual coefficient model. -/
theorem dualCoefficientSupportEquiv_smul (g : GKS K S) (x : MinS hS W i (charInv α)) :
    dualCoefficientSupportEquiv hS W i α hFull (g • x) =
      g • dualCoefficientSupportEquiv hS W i α hFull x := by
  have h := coefficientSupportEquiv_smul hS W i (charInv α) hFull g x
  rw [characterAfterSupport_charInv] at h
  exact h

/-- The coefficient identifications carry the actual Weil pairing to the
actual stage pairing, with its cyclotomic normalization carried along. -/
theorem coefficientSupportEquiv_pairing
    (x : MinS hS W i α) (y : MinS hS W i (charInv α)) :
    weilPairingData W i (characterAfterSupport hS i α) hμ
        (coefficientSupportEquiv hS W i α hFull x)
        (dualCoefficientSupportEquiv hS W i α hFull y) =
      tateSupportEquiv hμ₀ hμ (Acoef i) hS (actLBeta hS W i α hμ₀ x y) := by
  change weilA (S := S) W hμ (Acoef i)
      ((torsionSupportMap hS W (2 ^ i)).toIntLinearMap.baseChange (Acoef i)
        (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from x))
      ((torsionSupportMap hS W (2 ^ i)).toIntLinearMap.baseChange (Acoef i)
        (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from y)) =
    (supportUnit hμ₀ hμ (Acoef i) : Acoef i) *
      weilA (S := S₀) W hμ₀ (Acoef i)
        (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from x)
        (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from y)
  exact weilA_afterSupport hS W (2 ^ i) hμ₀ hμ (Acoef i) x y

end StageFrames

end ZInQ.Contrib.RC53Assist.OldOrthogonality.SupportCoefficients



/-!
# Transport of a local complement comparison

A coefficient identification induces an isomorphism on local cochains and on
the condition cone. Transport of the cup-product evaluation, including its
trace normalization, therefore transports the actual complement comparison.
-/

set_option maxHeartbeats 600000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.OldOrthogonality.LocalTransport

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy)

variable {R : Type} [CommRing R]

/-- A degreewise linear isomorphism commuting with the actual differentials. -/
structure ComplexIso (C D : GCx R) where
  e : ∀ n, C.X n ≃ₗ[R] D.X n
  comm : ∀ i j (h : i + 1 = j) (x : C.X i), e j (C.d i j h x) = D.d i j h (e i x)

/-- The forward chain map. -/
def ComplexIso.hom {C D : GCx R} (E : ComplexIso C D) : GHom C D where
  f i j h := by subst h; exact (E.e i).toLinearMap
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    exact E.comm i i₁ h₁ x

/-- The inverse chain map. -/
def ComplexIso.inv {C D : GCx R} (E : ComplexIso C D) : GHom D C where
  f i j h := by subst h; exact (E.e i).symm.toLinearMap
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    apply (E.e i₁).injective
    change (E.e i₁) ((E.e i₁).symm (D.d i i₁ h₁ x)) =
      (E.e i₁) (C.d i i₁ h₂ ((E.e i).symm x))
    rw [LinearEquiv.apply_symm_apply, E.comm, LinearEquiv.apply_symm_apply]

/-- The corresponding isomorphism of cochain complexes. -/
def ComplexIso.toCCIso {C D : GCx R} (E : ComplexIso C D) : C.toCC ≅ D.toCC where
  hom := GHom.toCC E.hom
  inv := GHom.toCC E.inv
  hom_inv_id := by
    ext n x
    exact (E.e n).symm_apply_apply x
  inv_hom_id := by
    ext n x
    exact (E.e n).apply_symm_apply x

/-- Transport of the actual condition map retains its source complex. -/
def ComplexIso.condition {C D U : GCx R} (E : ComplexIso C D) (ι : GHom U C) : GHom U D :=
  ghomComp ι E.hom

/-- The transported condition map is the actual cochain comparison after inclusion. -/
theorem ComplexIso.condition_apply {C D U : GCx R} (E : ComplexIso C D) (ι : GHom U C)
    (i j : ℤ) (h : i = j) (u : U.X i) :
    (E.condition ι).f i j h u = E.e j (ι.f i j h u) := by
  subst h
  rfl

/-- The induced isomorphism of the actual condition cones. -/
def ComplexIso.conditionCone {C D U : GCx R} (E : ComplexIso C D) (ι : GHom U C) :
    ComplexIso (coneCx (orthNeg ι)) (coneCx (orthNeg (E.condition ι))) where
  e n := LinearEquiv.prodCongr (LinearEquiv.refl R (U.X n)) (E.e (n - 1))
  comm i j hij c := by
    subst hij
    obtain ⟨u, x⟩ := c
    refine Prod.ext rfl ?_
    change E.e (i + 1 - 1) (-(ι.f i (i + 1 - 1) (by omega) u) -
      C.d (i - 1) (i + 1 - 1) (by omega) x) =
      -((E.condition ι).f i (i + 1 - 1) (by omega) u) -
        D.d (i - 1) (i + 1 - 1) (by omega) (E.e (i - 1) x)
    rw [map_sub, map_neg, E.comm, E.condition_apply]

section Complement

variable {U U' C C' D D' T T' : GCx R}
  (EA : ComplexIso C D) (EB : ComplexIso C' D')
  (ι : GHom U C) (ι' : GHom U' C')
  (P : GPair C C' T) (P' : GPair D D' T')
  (J : LocalTruncIsotropy ι ι' P)
  (J' : LocalTruncIsotropy (EA.condition ι) (EB.condition ι') P')
  (tr : T.X 2 →ₗ[R] R) (htr : ∀ z, tr (T.d 1 2 rfl z) = 0)
  (tr' : T'.X 2 →ₗ[R] R) (htr' : ∀ z, tr' (T'.d 1 2 rfl z) = 0)

/-- Evaluation compatibility identifies the transported local comparison,
not merely its source and target cohomology groups. -/
theorem localComparison_transport
    (heval : ∀ (n : ℤ) (u : U.X n) (x : C.X (n - 1)) (y : U'.X (3 - n)),
      tr' (P'.P (n - 1) (3 - n) 2 (by omega) (EA.e (n - 1) x)
          ((EB.condition ι').f (3 - n) (3 - n) rfl y) + J'.h n (3 - n) 2 (by omega) u y) =
        tr (P.P (n - 1) (3 - n) 2 (by omega) x (ι'.f (3 - n) (3 - n) rfl y) +
          J.h n (3 - n) 2 (by omega) u y)) :
    (EA.conditionCone ι).toCCIso.hom ≫
      GHom.toCC (orthLocalMap (EA.condition ι) (EB.condition ι') P' J' tr' htr') =
        GHom.toCC (orthLocalMap ι ι' P J tr htr) := by
  ext n c
  obtain ⟨u, x⟩ := c
  apply dualCx_ext
  intro y
  exact (orthLocalMap_apply (EA.condition ι) (EB.condition ι') P' J' tr' htr' n n rfl u
    (EA.e (n - 1) x) y).trans
    ((heval n u x y).trans (orthLocalMap_apply ι ι' P J tr htr n n rfl u x y).symm)

/-- A proved old complement comparison transports through the coefficient
identification and the exact cup-product evaluation compatibility. -/
theorem localComplement_transport
    (heval : ∀ (n : ℤ) (u : U.X n) (x : C.X (n - 1)) (y : U'.X (3 - n)),
      tr' (P'.P (n - 1) (3 - n) 2 (by omega) (EA.e (n - 1) x)
          ((EB.condition ι').f (3 - n) (3 - n) rfl y) + J'.h n (3 - n) 2 (by omega) u y) =
        tr (P.P (n - 1) (3 - n) 2 (by omega) x (ι'.f (3 - n) (3 - n) rfl y) +
          J.h n (3 - n) 2 (by omega) u y))
    (hOld : QuasiIso (GHom.toCC (orthLocalMap ι ι' P J tr htr))) :
    QuasiIso (GHom.toCC (orthLocalMap (EA.condition ι) (EB.condition ι') P' J' tr' htr')) := by
  have h := localComparison_transport EA EB ι ι' P P' J J' tr htr tr' htr' heval
  have heq : GHom.toCC (orthLocalMap (EA.condition ι) (EB.condition ι') P' J' tr' htr') =
      (EA.conditionCone ι).toCCIso.inv ≫ GHom.toCC (orthLocalMap ι ι' P J tr htr) := by
    rw [← h]
    simp
  haveI := hOld
  rw [heq]
  infer_instance

end Complement

section Coefficients

open ZInQ.Manuscript.RC.CoefModules

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M N : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [AddCommGroup N] [Module R N] [DistribMulAction G N] [SMulCommClass G R N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]

/-- A coefficient equivalence gives an isomorphism on the actual continuous
cochains, in every degree, including degree zero. -/
def coefficientCochainIso (e : M ≃ₗ[R] N)
    (he : ∀ (g : G) (m : M), e (g • m) = g • e m) :
    ComplexIso (natCx (contCochains R G M)) (natCx (contCochains R G N)) := by
  have hei : ∀ (g : G) (n : N), e.symm (g • n) = g • e.symm n := by
    intro g n
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
  let f := natHom (contCochainsMap (ContinuousMonoidHom.id G) e.toLinearMap
    continuous_of_discreteTopology he)
  let g := natHom (contCochainsMap (ContinuousMonoidHom.id G) e.symm.toLinearMap
    continuous_of_discreteTopology hei)
  have hgf : ∀ n (x : (natCx (contCochains R G M)).X n), g.f n n rfl (f.f n n rfl x) = x := by
    intro n x
    rcases n with n | n
    · apply Subtype.ext
      funext v
      change e.symm (e (cfun x v)) = cfun x v
      exact e.symm_apply_apply _
    · have : Subsingleton ((natCx (contCochains R G M)).X (Int.negSucc n)) :=
        inferInstanceAs (Subsingleton PUnit)
      exact Subsingleton.elim _ _
  have hfg : ∀ n (x : (natCx (contCochains R G N)).X n), f.f n n rfl (g.f n n rfl x) = x := by
    intro n x
    rcases n with n | n
    · apply Subtype.ext
      funext v
      change e (e.symm (cfun x v)) = cfun x v
      exact e.apply_symm_apply _
    · have : Subsingleton ((natCx (contCochains R G N)).X (Int.negSucc n)) :=
        inferInstanceAs (Subsingleton PUnit)
      exact Subsingleton.elim _ _
  refine ⟨fun n => LinearEquiv.ofLinearMap (f.f n n rfl) (g.f n n rfl)
    (LinearMap.ext (hfg n)) (LinearMap.ext (hgf n)), ?_⟩
  intro i j hij x
  exact f.comm i j i j rfl hij hij rfl x

end Coefficients

section CupTransport

open ZInQ.Manuscript.RC.CoefModules

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B T A' B' T' : Type}
  [AddCommGroup A] [Module R A] [DistribMulAction G A] [SMulCommClass G R A]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul G A]
  [AddCommGroup B] [Module R B] [DistribMulAction G B] [SMulCommClass G R B]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
  [AddCommGroup T] [Module R T] [DistribMulAction G T] [SMulCommClass G R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul G T]
  [AddCommGroup A'] [Module R A'] [DistribMulAction G A'] [SMulCommClass G R A']
  [TopologicalSpace A'] [DiscreteTopology A'] [ContinuousSMul G A']
  [AddCommGroup B'] [Module R B'] [DistribMulAction G B'] [SMulCommClass G R B']
  [TopologicalSpace B'] [DiscreteTopology B'] [ContinuousSMul G B']
  [AddCommGroup T'] [Module R T'] [DistribMulAction G T'] [SMulCommClass G R T']
  [TopologicalSpace T'] [DiscreteTopology T'] [ContinuousSMul G T']
  (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eT : T ≃ₗ[R] T')
  (heA : ∀ (g : G) (a : A), eA (g • a) = g • eA a)
  (heB : ∀ (g : G) (b : B), eB (g • b) = g • eB b)
  (heT : ∀ (g : G) (t : T), eT (g • t) = g • eT t)
  (β : A →ₗ[R] B →ₗ[R] T) (β' : A' →ₗ[R] B' →ₗ[R] T')
  (hβ : ∀ (g : G) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
  (hβ' : ∀ (g : G) (a : A') (b : B'), β' (g • a) (g • b) = g • β' a b)

/-- The cochain comparison preserves the actual cup product in every degree. -/
theorem coefficientCochainIso_cup
    (hpair : ∀ a b, eT (β a b) = β' (eA a) (eB b))
    (a b c : ℤ) (hab : a + b = c)
    (x : (globalCx R G A).X a) (y : (globalCx R G B).X b) :
    (coefficientCochainIso eT heT).e c
        ((globalPair R G β hβ (continuous_pairing β)).P a b c hab x y) =
      (globalPair R G β' hβ' (continuous_pairing β')).P a b c hab
        ((coefficientCochainIso eA heA).e a x) ((coefficientCochainIso eB heB).e b y) := by
  rcases a with a | a
  · rcases b with b | b
    · obtain rfl : c = ((a + b : ℕ) : ℤ) := by
        simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using hab.symm
      apply Subtype.ext
      funext g
      change eT (cupFun β a b (a + b) rfl (cFun x) (cFun y) g) =
        cupFun β' a b (a + b) rfl (fun v => eA (cFun x v)) (fun v => eB (cFun y v)) g
      rw [cupFun_apply, cupFun_apply, hpair, heB]
    · have : Subsingleton ((globalCx R G B).X (Int.negSucc b)) := inferInstanceAs (Subsingleton PUnit)
      rw [Subsingleton.elim y 0]
      simp only [map_zero, LinearMap.zero_apply]
  · have : Subsingleton ((globalCx R G A).X (Int.negSucc a)) := inferInstanceAs (Subsingleton PUnit)
    rw [Subsingleton.elim x 0]
    simp only [map_zero, LinearMap.zero_apply]

end CupTransport

section Traces

variable {C D : GCx R} (E : ComplexIso C D) (tr : D.X 2 →ₗ[R] R)

/-- Pullback of the trace along the exact cyclotomic cochain comparison. -/
def ComplexIso.pullTrace : C.X 2 →ₗ[R] R := tr ∘ₗ (E.e 2).toLinearMap

/-- Pullback preserves the vanishing on coboundaries. -/
theorem ComplexIso.pullTrace_kills (htr : ∀ z, tr (D.d 1 2 rfl z) = 0) :
    ∀ z, E.pullTrace tr (C.d 1 2 rfl z) = 0 := by
  intro z
  change tr (E.e 2 (C.d 1 2 rfl z)) = 0
  rw [E.comm]
  exact htr _

/-- Pullback preserves the full degree-two trace isomorphism. -/
theorem ComplexIso.pullTrace_induces (htr : InducesIsoH2 tr) : InducesIsoH2 (E.pullTrace tr) := by
  constructor
  · intro z hz hzero
    have hz' : D.d 2 3 rfl (E.e 2 z) = 0 := by
      rw [← E.comm, hz, map_zero]
    obtain ⟨y, hy⟩ := htr.1 _ hz' hzero
    refine ⟨(E.e 1).symm y, ?_⟩
    apply (E.e 2).injective
    rw [E.comm, LinearEquiv.apply_symm_apply, hy]
  · obtain ⟨z, hz, hzr⟩ := htr.2
    refine ⟨(E.e 2).symm z, ?_, ?_⟩
    · apply (E.e 3).injective
      rw [E.comm, LinearEquiv.apply_symm_apply, hz, map_zero]
    · change tr (E.e 2 ((E.e 2).symm z)) = 1
      rw [LinearEquiv.apply_symm_apply, hzr]

end Traces

section ZeroComparisons

variable {U U' C C' E D D' F : GCx R}

/-- Naturality of the local comparison when both truncated homotopies vanish
in total degree three. The cup product is transported in all degrees. -/
theorem localComplement_transport_zero
    (EA : ComplexIso C D) (EB : ComplexIso C' D') (ET : ComplexIso E F)
    (ι : GHom U C) (ι' : GHom U' C') (P : GPair C C' E) (P' : GPair D D' F)
    (J : LocalTruncIsotropy ι ι' P)
    (J' : LocalTruncIsotropy (EA.condition ι) (EB.condition ι') P')
    (tr : F.X 2 →ₗ[R] R) (htr : ∀ z, tr (F.d 1 2 rfl z) = 0)
    (hJ : ∀ a b (hab : a + b = 3) (u : U.X a) (y : U'.X b), J.h a b 2 hab u y = 0)
    (hJ' : ∀ a b (hab : a + b = 3) (u : U.X a) (y : U'.X b), J'.h a b 2 hab u y = 0)
    (hPair : ∀ a b c (hab : a + b = c) (x : C.X a) (y : C'.X b),
      ET.e c (P.P a b c hab x y) = P'.P a b c hab (EA.e a x) (EB.e b y))
    (hOld : QuasiIso (GHom.toCC (orthLocalMap ι ι' P J (ET.pullTrace tr) (ET.pullTrace_kills tr htr)))) :
    QuasiIso (GHom.toCC (orthLocalMap (EA.condition ι) (EB.condition ι') P' J' tr htr)) := by
  apply localComplement_transport EA EB ι ι' P P' J J' (ET.pullTrace tr)
    (ET.pullTrace_kills tr htr) tr htr ?_ hOld
  intro n u x y
  rw [hJ, hJ', add_zero, add_zero, EB.condition_apply]
  rw [← hPair]
  rfl

end ZeroComparisons

end ZInQ.Contrib.RC53Assist.OldOrthogonality.LocalTransport


namespace ZInQ.Contrib.RC53Assist.OldOrthogonality.StageOrthogonality

set_option maxHeartbeats 800000

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy MilneLocalTateDualityKummerCharZero)
open ZInQ.Contrib.RC53Assist.OldOrthogonality.SupportCoefficients
open ZInQ.Contrib.RC53Assist.OldOrthogonality.LocalTransport
open ZInQ.Contrib.RC53Assist.OldOrthogonality.Truncations

variable {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  (hFull : FullTorsion K S₀ W (2 ^ i))
  (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i)) (hμ : HasRootsOfUnity K S (2 ^ i))

/-- The actual local coefficient comparison in the first slot. -/
def localSupportA (v : Places K S) :
    ComplexIso (locAt K S (Acoef i) (MinS hS W i α) v)
      (locAt K S (Acoef i) (Mcoef K S W i (characterAfterSupport hS i α)) v) := by
  let e : ResMod (locMap K S v.1) (MinS hS W i α) ≃ₗ[Acoef i]
      ResMod (locMap K S v.1) (Mcoef K S W i (characterAfterSupport hS i α)) :=
    coefficientSupportEquiv hS W i α hFull
  exact coefficientCochainIso (G := Gloc K v.1) e
    (fun g x => coefficientSupportEquiv_smul hS W i α hFull (locMap K S v.1 g) x)

/-- The actual local coefficient comparison in the dual slot. -/
def localSupportB (v : Places K S) :
    ComplexIso (locAt K S (Acoef i) (MinS hS W i (charInv α)) v)
      (locAt K S (Acoef i) (Mcoef K S W i (charInv (characterAfterSupport hS i α))) v) := by
  let e : ResMod (locMap K S v.1) (MinS hS W i (charInv α)) ≃ₗ[Acoef i]
      ResMod (locMap K S v.1) (Mcoef K S W i (charInv (characterAfterSupport hS i α))) :=
    dualCoefficientSupportEquiv hS W i α hFull
  exact coefficientCochainIso (G := Gloc K v.1) e
    (fun g x => dualCoefficientSupportEquiv_smul hS W i α hFull (locMap K S v.1 g) x)

/-- The local cyclotomic comparison carries its normalization unit. -/
def localSupportT (v : Places K S) :
    ComplexIso (locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) v)
      (locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v) := by
  let e : ResMod (locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) ≃ₗ[Acoef i]
      ResMod (locMap K S v.1) (Tate1 (Acoef i) hμ) := tateSupportEquiv hμ₀ hμ (Acoef i) hS
  exact coefficientCochainIso (G := Gloc K v.1) e
    (fun g x => tateSupportEquiv_smul hμ₀ hμ (Acoef i) hS (locMap K S v.1 g) x)

/-- The coefficient dictionaries preserve the actual local Weil cup product. -/
theorem localSupport_cup (v : Places K S) (a b c : ℤ) (hab : a + b = c)
    (x : (locAt K S (Acoef i) (MinS hS W i α) v).X a)
    (y : (locAt K S (Acoef i) (MinS hS W i (charInv α)) v).X b) :
    (localSupportT hS i hμ₀ hμ v).e c
        ((orthGaloisPair K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀) v).P a b c hab x y) =
      (orthGaloisPair K (weilPairingData W i (characterAfterSupport hS i α) hμ)
        (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α)) v).P a b c hab
        ((localSupportA hS W i α hFull v).e a x) ((localSupportB hS W i α hFull v).e b y) := by
  have : SMulCommClass (GKS K S) (Acoef i) (MinS hS W i α) :=
    inferInstanceAs (SMulCommClass (GKS K S) (Acoef i) (InflMod hS (Mcoef K S₀ W i α)))
  have : SMulCommClass (GKS K S) (Acoef i) (MinS hS W i (charInv α)) :=
    inferInstanceAs (SMulCommClass (GKS K S) (Acoef i) (InflMod hS (Mcoef K S₀ W i (charInv α))))
  let eA : ResMod (locMap K S v.1) (MinS hS W i α) ≃ₗ[Acoef i]
      ResMod (locMap K S v.1) (Mcoef K S W i (characterAfterSupport hS i α)) :=
    coefficientSupportEquiv hS W i α hFull
  let eB : ResMod (locMap K S v.1) (MinS hS W i (charInv α)) ≃ₗ[Acoef i]
      ResMod (locMap K S v.1) (Mcoef K S W i (charInv (characterAfterSupport hS i α))) :=
    dualCoefficientSupportEquiv hS W i α hFull
  let eT : ResMod (locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) ≃ₗ[Acoef i]
      ResMod (locMap K S v.1) (Tate1 (Acoef i) hμ) := tateSupportEquiv hμ₀ hμ (Acoef i) hS
  exact coefficientCochainIso_cup
    (R := Acoef i) (G := Gloc K v.1)
    (A := ResMod (locMap K S v.1) (MinS hS W i α))
    (B := ResMod (locMap K S v.1) (MinS hS W i (charInv α)))
    (T := ResMod (locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (A' := ResMod (locMap K S v.1) (Mcoef K S W i (characterAfterSupport hS i α)))
    (B' := ResMod (locMap K S v.1) (Mcoef K S W i (charInv (characterAfterSupport hS i α))))
    (T' := ResMod (locMap K S v.1) (Tate1 (Acoef i) hμ))
    eA eB eT
    (fun g x => coefficientSupportEquiv_smul hS W i α hFull (locMap K S v.1 g) x)
    (fun g x => dualCoefficientSupportEquiv_smul hS W i α hFull (locMap K S v.1 g) x)
    (fun g x => tateSupportEquiv_smul hμ₀ hμ (Acoef i) hS (locMap K S v.1 g) x)
    (resPairing (Acoef i) (GKS K S) (actLBeta hS W i α hμ₀) (locMap K S v.1))
    (resPairing (Acoef i) (GKS K S) (weilPairingData W i (characterAfterSupport hS i α) hμ) (locMap K S v.1))
    (fun g x y => actLBeta_smul hS W i α hμ₀ (locMap K S v.1 g) x y)
    (fun g x y => weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α) (locMap K S v.1 g) x y)
    (fun x y => (coefficientSupportEquiv_pairing hS W i α hFull hμ₀ hμ x y).symm)
    a b c hab x y

variable (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (P : Set (HeightOneSpectrum (𝓞 K)))
  (hα : ∀ v ∈ P, IsLocallyQuadAt i α (quadChar s hs hs0) v)

/-- The actual old condition in the exact first-stage coefficient model. -/
def transportedOldA (v : Places K S) :
    CondAt K S (Acoef i) (Mcoef K S W i (characterAfterSupport hS i α)) v :=
  ⟨(actLCondA hS W i s hs hs0 hFull P α hα v).U,
    (localSupportA hS W i α hFull v).condition (actLCondA hS W i s hs hs0 hFull P α hα v).i⟩

/-- The actual dual old condition in the exact dual-stage coefficient model. -/
def transportedOldB (v : Places K S) :
    CondAt K S (Acoef i) (Mcoef K S W i (charInv (characterAfterSupport hS i α))) v :=
  ⟨(actLCondB hS W i s hs hs0 hFull P α hα v).U,
    (localSupportB hS W i α hFull v).condition (actLCondB hS W i s hs hs0 hFull P α hα v).i⟩

/-- Old Kummer and unramified complexes live in degrees zero and one;
old full conditions have a zero dual condition. Thus no degree-three
homotopy value contributes to the local comparison. -/
theorem transportedOld_h_zero (v : Places K S)
    (J : LocalTruncIsotropy
      (transportedOldA hS W i α hFull s hs hs0 P hα v).i
      (transportedOldB hS W i α hFull s hs hs0 P hα v).i
      (orthGaloisPair K (weilPairingData W i (characterAfterSupport hS i α) hμ)
        (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α)) v))
    (a b : ℤ) (hab : a + b = 3)
    (u : (actLCondA hS W i s hs hs0 hFull P α hα v).U.X a)
    (y : (actLCondB hS W i s hs hs0 hFull P α hα v).U.X b) : J.h a b 2 hab u y = 0 := by
  classical
  by_cases hv : v.1 ∈ S₀
  · by_cases hp : v.1 ∈ P
    · have hA : OrthConcentratedAt (actLCondA hS W i s hs hs0 hFull P α hα v) := by
        rw [actLCondA_of_P hS W i s hs hs0 hFull P α hα hv hp]
        have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
        exact orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
          (kummerIotaS hS W i s hs hs0 α hFull v) (kummerIotaS_smul hS W i s hs hs0 α hFull v (hα v.1 hp))
      have hB : OrthConcentratedAt (actLCondB hS W i s hs hs0 hFull P α hα v) := by
        rw [actLCondB_of_P hS W i s hs hs0 hFull P α hα hv hp]
        have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
        exact orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
          (kummerIotaS hS W i s hs hs0 (charInv α) hFull v)
          (kummerIotaS_smul hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv (hα v.1 hp)))
      exact orthLD_h_zero _ _ _ J hA hB a b hab u y
    · have hB : Subsingleton ((actLCondB hS W i s hs hs0 hFull P α hα v).U.X b) := by
        rw [actLCondB_of_notP hS W i s hs hs0 hFull P α hα hv hp]
        exact inferInstanceAs (Subsingleton PUnit)
      rw [Subsingleton.elim y 0]
      exact (J.h a b 2 hab u).map_zero
  · have hA : OrthConcentratedAt (actLCondA hS W i s hs hs0 hFull P α hα v) := by
      rw [actLCondA_of_notS0 hS W i s hs hs0 hFull P α hα hv]
      exact orth_urAt_vanishes hS (Acoef i) (Mcoef K S₀ W i α) v hv
    have hB : OrthConcentratedAt (actLCondB hS W i s hs hs0 hFull P α hα v) := by
      rw [actLCondB_of_notS0 hS W i s hs hs0 hFull P α hα hv]
      exact orth_urAt_vanishes hS (Acoef i) (Mcoef K S₀ W i (charInv α)) v hv
    exact orthLD_h_zero _ _ _ J hA hB a b hab u y

/-- The unchanged arithmetic conditions with strict derivative truncations,
in the exact coefficient model of the stage consumer. -/
def actualStageA (Q : Finset (Places K S)) :
    GaloisLocalConditions K S (Acoef i) (Mcoef K S W i (characterAfterSupport hS i α)) :=
  ofCondAt K S (Acoef i) (Mcoef K S W i (characterAfterSupport hS i α))
    (strictOverrideAt Q (transportedOldA hS W i α hFull s hs hs0 P hα))

/-- The unchanged dual arithmetic conditions with relaxed derivative truncations. -/
def actualStageB (Q : Finset (Places K S)) :
    GaloisLocalConditions K S (Acoef i) (Mcoef K S W i (charInv (characterAfterSupport hS i α))) :=
  ofCondAt K S (Acoef i) (Mcoef K S W i (charInv (characterAfterSupport hS i α)))
    (relaxedOverrideAt Q (transportedOldB hS W i α hFull s hs hs0 P hα))


end ZInQ.Contrib.RC53Assist.OldOrthogonality.StageOrthogonality
