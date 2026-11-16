# pic-fix log

Base: wip/pic-dict 4e95795b + merge of origin/main (2880fef1e) = 5f3b22f2d. Build tree copied from ~/dzq-check2
(at 2880fef1e); `lake build ZInQKernel.Contrib.OneProof.PicDictionary` OK (12811 jobs, 3 min).

## (1) KLFinite, printed form

* New leaf `PicFix.MumfordKLFiniteSectionAC`: k = k̄, X : AbVar k, c₀ ample with a nonzero global section
  `s : 𝟙 ⟶ modX c₀` ⇒ `{x | phi c₀ x = 1}` finite (Mumford §6 App. 1, (iv) ⇒ (ii), L = 𝒪(D), D effective).
* Glue proved (scratch/pic-fix/KLSection.lean), VERIFIED compiled, axioms [propext, Classical.choice, Quot.sound]:
  * `mk_tensorPow`: [M^{⊗n}] = [M]^n;
  * `support_tensorPowSection`: supp Z(s^{⊗m}) = supp Z(s), m > 0 (local generator, vendored
    `exists_tensorPowSectionOne_eq_pow_smul`, `Hom.ideal_zeroLocus`, Mathlib `basicOpen_pow`);
  * `isAmple_pow`: IsAmple c ⇒ IsAmple (c^n), n > 0;
  * `exists_pow_section`: ample on nonempty X ⇒ some c^m (m > 0) has a nonzero section (`zeroLocus_eq_bot_iff`);
  * `phi_pow`: φ_{L^n}(x) = φ_L(x)^n, so K(L) ⊆ K(L^n) (no theorem of the square needed);
  * `mumfordKLFiniteAC_of_section : MumfordKLFiniteSectionAC → MumfordKLFiniteAC`;
  * `phiAmpleIsogeny_of_printed (hKL : MumfordKLFiniteSectionAC) (h8 : MumfordPhiSurjectiveAC) : PhiAmpleIsogeny`.
* picZeroPtsTranslInv: not an assumption of phiAmpleIsogeny_final (already a theorem in PicDictionary,
  `picZeroPtsTranslInv_of_leaves` with `pushforwardUnitUniversal`, `geomIntegralProd` proved). It is used for
  surjectivity, not finiteness, so the restatement does not touch it.
