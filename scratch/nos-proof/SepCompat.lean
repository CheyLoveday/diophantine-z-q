import ZInQKernel.Contrib.OneProof.NeronOggShafarevich

/-! # nos-proof: dict-galois's leaf `NOSSepDict.NeronOggShafarevichSep` from `NOSProof.NOSConverseSep`

`NeronOggShafarevichSepCopy` is a verbatim copy of dict-galois's def (`ZInQKernel/Contrib/OneProof/
NeronOggShafarevichSep.lean` on wip/dict-galois 81d1f67f), restated because that file is not on main. If
dict-galois's fold lands first (replacing `r7a` by `neronOggShafarevichSep`), this theorem discharges that field
from `NOSConverseSep` (the copy and the original are the same term, so `h` closes either by `exact`). -/

open CategoryTheory AlgebraicGeometry
open PkgI2 (IsAbelianVariety HasGoodReduction InertiaTrivialOn)

namespace NOSSepCompat

def NeronOggShafarevichSepCopy : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ks : Type) [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]
    (w : ValuationSubring Ks), w.comap (algebraMap K Ks) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      (HasGoodReduction A O ↔
        ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m) ∧
      (HasGoodReduction A O ↔
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite)

theorem neronOggShafarevichSep_of_converse (h : NOSProof.NOSConverseSep) : NeronOggShafarevichSepCopy := by
  intro K _ O _ Ks _ _ _ w hw A _
  have hca := h K O Ks w hw A
  have hab : HasGoodReduction A O → ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m :=
    fun hA m _ hu => NOSProof.inertiaTrivialOn_of_goodReduction_any O Ks w hw A hA m hu
  have hbc : (∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m) →
      {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite := by
    intro hb
    refine (NOSProof.infinite_natCast_isUnit O).mono ?_
    rintro m ⟨hm, hu⟩
    exact ⟨hm, hu, hb m hm hu⟩
  exact ⟨⟨hab, fun hb => hca (hbc hb)⟩, ⟨fun hA => hbc (hab hA), hca⟩⟩

end NOSSepCompat

#print axioms NOSSepCompat.neronOggShafarevichSep_of_converse
