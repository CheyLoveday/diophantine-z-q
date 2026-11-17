p='ZInQKernel/Contrib/OneProof/R16IsJ1Dict.lean'
s=open(p).read()
def rep(a,b):
    global s
    assert a in s, a[:80]
    s=s.replace(a,b)
# strong Pic0 leaf
rep("""    ∃ X : Over SpecQ, IsX1Model N X ∧
      ∀ (V : AbelianVariety ℚ) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
        PicardTensorCompatible X.hom V.group rep → AfTateAt N χ f (ofVendored V)""",
"""    ∃ X : Over SpecQ, IsX1Model N X ∧
      ∃ (V : AbelianVariety ℚ) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
        PicardTensorCompatible X.hom V.group rep ∧ AfTateAt N χ f (ofVendored V)""")
rep("""    ∃ X : Over SpecQ, IsX1Model N X ∧
      ∀ (V : AbelianVariety ℚ) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
        PicardTensorCompatible X.hom V.group rep → AfTateWeakOddAt N χ f (ofVendored V)""",
"""    ∃ X : Over SpecQ, IsX1Model N X ∧
      ∃ (V : AbelianVariety ℚ) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
        PicardTensorCompatible X.hom V.group rep ∧ AfTateWeakOddAt N χ f (ofVendored V)""")
old_use="""  obtain ⟨X₀, ⟨hXc₀, hXi₀, P₀', hP₀', ⟨eX₀⟩⟩, hA⟩ := h N χ f hN hf"""
new_use="""  obtain ⟨X₀, ⟨hXc₀, hXi₀, P₀', hP₀', ⟨eX₀⟩⟩, V, rep, htc, hA⟩ := h N χ f hN hf"""
assert s.count(old_use)==2
s=s.replace(old_use,new_use)
old2="""  obtain ⟨V, rep, htc⟩ := exists_picZero X₀ hXc₀
  exact (hA V rep htc).of_iso"""
assert s.count(old2)==2
s=s.replace(old2,"""  exact hA.of_iso""")
rep("""  obtain ⟨X, P₀, hX⟩ := hx N hN
  refine ⟨X, hX, fun V rep htc => ?_⟩
  obtain ⟨aj, hJ⟩ := isJacobian_picZero X hX.1 V rep htc P₀
  exact h N χ f (ofVendored V) hN hf ⟨X, P₀, aj, hX, hJ⟩""","""  obtain ⟨X, P₀, hX⟩ := hx N hN
  obtain ⟨V, rep, htc⟩ := exists_picZero X hX.1
  refine ⟨X, hX, V, rep, htc, ?_⟩
  obtain ⟨aj, hJ⟩ := isJacobian_picZero X hX.1 V rep htc P₀
  exact h N χ f (ofVendored V) hN hf ⟨X, P₀, aj, hX, hJ⟩""")
rep("""  obtain ⟨X, P₀, hX⟩ := hx N hN
  refine ⟨X, hX, fun V rep htc => ?_⟩
  obtain ⟨aj, hJ⟩ := isJacobian_picZero X hX.1 V rep htc P₀
  exact weakOdd_of_afTate""","""  obtain ⟨X, P₀, hX⟩ := hx N hN
  obtain ⟨V, rep, htc⟩ := exists_picZero X hX.1
  refine ⟨X, hX, V, rep, htc, ?_⟩
  obtain ⟨aj, hJ⟩ := isJacobian_picZero X hX.1 V rep htc P₀
  exact weakOdd_of_afTate""")
s=s.replace("(any representing abelian\nvariety with the tensor group law) satisfies","(some representing abelian\nvariety with the tensor group law) satisfies")
s=s.replace("scheme `J₁(N) = Pic⁰_{X/ℚ}` (any representing abelian variety `V` with the tensor group law) there are","scheme `J₁(N) = Pic⁰_{X/ℚ}` (some representing abelian variety `V` with the tensor group law) there are")
open(p,'w').write(s)
print("ok")
