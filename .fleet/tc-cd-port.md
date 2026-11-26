# tc-cd-port (fleet note)

- Both roots build: ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.CohomologicalDimension.AbsoluteGaloisGroup
  and ...Local.Duality.FiniteModule (lake build, no errors).
- Target builds: `TauCeti.ClassFieldTheory.cohomologicalDimensionAt_absoluteGaloisGroup_eq_two :
  ∀ {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  (ℓ : ℕ) [Fact (Nat.Prime ℓ)], TauCeti.cohomologicalDimensionAt ℓ (Field.absoluteGaloisGroup K) = 2`.
  #print axioms: [propext, Classical.choice, Quot.sound]. The same holds for
  dualityMap_bijective_of_smul_kummerCoeff_eq_self, cohomologicalDimensionAt_le_iff and
  subsingleton_continuousCohomology_ofDiscreteModule_iff.
- New modules: 103 (closure union 521, 418 already vendored; scratch/tc-cd-port/modules.txt).
  Locally changed files: 0. MathlibBackport additions: 0. No count change.
- Clash: both roots together with the 53 existing TauCeti top modules compile with no clash.
  The variant with ZInQKernel.OneProof.Main (scratch/tc-cd-port/Clash.lean) was not run,
  because building OneProof.Main's closure hit the 2-hour background limit. A static check of the
  1259 new declaration names against the non-TauCeti sources finds no clash. Remaining:
  the integrator can run Clash.lean once OneProof.Main is built.
- Diff against the base: only added files, plus the appended Source entry in ThirdParty/TauCeti/NOTICE.
- Contributor draft (1f3ef0e3) not in the local repository: cross-check skipped.
- Build: cold 8 min 26 s for 523 modules (4 threads); warm rebuild 2.6 s.
- AllContrib not touched (left to the lead's integration chain).
- Report: docs/research/tc-cd-port.md.
