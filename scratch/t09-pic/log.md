# t09-pic results log

Field: `t09SymmIsogenyExists : HDec.WeilPairing.T09_SymmIsogenyExists`
(`∀ K A, Nonempty (SymmIsogeny A)`), Mumford §§6, 8, 20, 23.

## Setup
- `lake build ZInQKernel.Hypotheses.JHeight` once (builds upstream `lean/` helpers; else "unknown module prefix 'ZInQ'").
- Check: `lake env lean scratch/t09-pic/Pic.lean` (imports TailB + vendored Picard/QuasiProjective/Twist + FrobChain.Rigidity).

## Compile outcomes
- 2026-11-14 17:58 Pic.lean v1 (§0 verbatim copy + rfl; mumfordBundle, phiL, identityComponent, IsPicZero,
  IsVeryAmple; `exists_isVeryAmple` proved): 0 errors. VERIFIED.
- 2026-11-14 18:10 Pic.lean v2: `comp_classify`, `mumfordBundle_restrict_zero`, `eta_comp_phiL` (φ_L(0)=0 for the Picard group law) proved: 0 errors. VERIFIED.
- 2026-11-14 18:20 Pic.lean v3: `exists_hom_comp_eq_phiL` (φ_L = λ_L ≫ ι with λ_L : Hom A B, for any (B, ι) with IsPicZero) proved: 0 errors. VERIFIED.
- 2026-11-14 18:30 Pic.lean v4: leaves L1 `PicRepresentableAbVar`, L2 `PicZeroAbVar`, L3 `PhiVeryAmpleIsogeny`,
  L4 `WeilPairingPicZero`; `t09SymmIsogenyExists_of_leaves : L1 → L2 → L3 → L4 → HDec.WeilPairing.T09_SymmIsogenyExists`:
  0 errors; `#print axioms` of exists_isVeryAmple, eta_comp_phiL, exists_hom_comp_eq_phiL,
  t09SymmIsogenyExists_of_leaves: [propext, Classical.choice, Quot.sound]. VERIFIED.

## Statements (Pic.lean)
- Genuine defs: `mumfordBundle A L = m^*L * (p₁^*L)⁻¹ * (p₂^*L)⁻¹ ∈ Pic(A ×_K A)`;
  `phiL rep L := rep.homEquiv.symm (toPicardFunctor.app (op A.X) (mumfordBundle A L)) : A.X ⟶ P`;
  `identityComponent G` = connected component of the unit point; `IsPicZero rep B j` = open immersion onto the identity
  component + IsMonHom (group law `picardFunctorCommGrpObj`); `IsVeryAmple A L` = `L = i^*𝒪(1)` for an immersion
  `i : A → ℙ(N; Spec K)` over K, N finite.
- Glue proved: `exists_isVeryAmple` (vendored projective immersion), `comp_classify` (Yoneda naturality),
  `mumfordBundle_restrict_zero` (Λ(L)|_{A×0} = 1, uses Pic(Spec K) = 1), `eta_comp_phiL` (φ_L(0)=0),
  `exists_hom_comp_eq_phiL` (A connected ⇒ φ_L lands in the identity component; lift through the open immersion;
  homomorphism by `MulRigidity.isMonHom_of_geometricallyIntegral`).
