# hecke-pin results log

## Reading (VERIFIED, pdftotext of both local DS printings)
- DS Thm 9.6.5: 2005 printing p. 393; 2016 fourth printing p. 404. The sentence *right after* the theorem is about
  the determinant ("The characteristic equation shows that det ρ = ..."). The relevant sentence is two
  paragraphs later, same page in both printings: "Section 9.5 constructed ρf,λ when k = 2 but didn't prove
  that ρf,λ is irreducible or that the equation is the characteristic equation."
  Verdict: it identifies the §9.5 construction as the k = 2 case of 9.6.5's ρf,λ (same name, "constructed ρf,λ
  when k = 2"), so 9.6.5 at k = 2 asserts the characteristic equation for the §9.5 representation; the
  sentence itself gives no proof or reference for that (it flags that §9.5 did not prove it).
- DS Thm 6.1.2 (Abel's Theorem), 2005 p. 214: Pic^0(X) ≅ Jac(X) by Σ n_x ∫_{x0}^{x}. (locator for AbelJacobiX1)
- DS §7.7, 2005 pp. 290-291: X1(N) = X1(N)_alg,C up to C-isomorphism, function field C(j, f1), via Thm 7.7.1
  and Thm 7.2.5. (locator for X1TauPoints)

## Plan / statements
- New file ZInQKernel/Contrib/OneProof/HeckePin.lean (namespace AfTateLam.HeckePin). VERIFIED: `lake build
  ZInQKernel.Contrib.OneProof.HeckePin` succeeds (02:07).
  * gap 3: coeff_zero_eq, coeff_mem_genField (a_n ∈ ℚ(a_p, χ(d)) from IsNormalizedEigenform), theta_unique. No extra input.
  * gap 2b: hom_ext_of_isAfQuotient, isAfQuotient_unique (unique iso compatible with π), induced_comm. No extra input.
  * gap 1: heckeD (free algebra on Div(ℍ)), cls_heckeD (Claim A), psi_heckeD (Claim B),
    evF_eq_zero_of_heckeJ_eq_zero : X1TauPoints → AbelJacobiX1 → EichlerPrimitive → EichlerHecke → ... →
    heckeJ h = 0 → evF h = 0; evF_wellDefined, image_ker_evF_eq_IfDS, killsIf_iff_IfDS.
  * gap 2a: isHeckeT_agree, isDiamond_agree (need only TauPts), end_eq_of_classes (ConstOnTauPoints + Albanese),
    isHeckeT_unique, isDiamond_unique.
- New Props: X1TauPoints (leaf candidate, DS §7.7), AbelJacobiX1 (leaf candidate, DS Thm 6.1.2 + Milne JV),
  EichlerPrimitive (GLUE), EichlerHecke (GLUE), ConstOnTauPoints (GLUE).
- 02:16 EichlerPrimitive PROVED (eichlerPrimitive: Morera on unit disc for dslope(cuspFunction) + q-substitution).
- EichlerHecke PROVED (eichlerHecke): hecke_eigen_fun (T_p f = a_p f from q-expansion, sum_exp_shift, reindex
  m ↦ pm, coeff_rec_prime), eichler_heckeT / eichler_diamond (derivative zero on ℍ, nebentypus, SL_slash_apply).
- evF_eq_zero_of_heckeJ_eq_zero_of_leaves, killsIf_iff_IfDS_of_leaves: gap 1 from X1TauPoints + AbelJacobiX1 only.
- Axioms (scratch/hecke-pin/Axioms-output.txt): all main theorems [propext, Classical.choice, Quot.sound]. VERIFIED.
- Target.lean: verbatim copies of HeckeJ1DS, AfShimura, AfCharpolyDS965 + dependencies; Iff.rfl. VERIFIED.
- Discharges-output.txt: r16CoreY still by r16CoreY_of_ds965; HeckePin discharges no field (audit lemmas). VERIFIED.
- autofold.json = r16-det spec + audit docs + audit_props; dry run 11/18 on 29 -> 15/17 on 32 (unchanged);
  FoldDryRun.lean sixContactMin_of_open49 standard axioms. VERIFIED.
- Leaf docstrings (HeckeJ1DS, AfShimura, AfCharpolyDS965) now point at HeckePin.lean (text only); build OK.
