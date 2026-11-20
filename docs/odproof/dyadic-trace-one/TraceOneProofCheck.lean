import ZInQKernel.Contrib.RC53Assist.PlaceAboveTwo.TraceOne

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.DKLocalAdapter
open ZInQ.Contrib.RC53Assist.PlaceAboveTwo

-- Check the existing trace and its literal degree-two predicate with no extra proof input.
example {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (W : WeierstrassCurve K) [W.IsElliptic] [HasFullTwoTorsion K S W]
    (w : {v : HeightOneSpectrum (𝓞 K) // (2 : 𝓞 K) ∈ v.asIdeal})
    [DecidableEq (w.val.adicCompletion K)] :
    InducesIsoH2 (C := natCx (restrictedLineComplex (S := S) w.val))
      (orientedLocalTrace (S := S) W w.val) :=
  orientedTrace_inducesIsoH2 W w

#print axioms SignLine.invariant_normalization
#print axioms SignLine.finiteInvariant_kummerClass
#print axioms SignLine.exists_local_trace
#print axioms SignLine.duality02
#print axioms SignLine.trace_duality02
#print axioms exists_normalized_cycle
#print axioms first_reduction_eq_sign_iff
#print axioms exists_trace_one_with_sign
#print axioms orientedTraceOne
#print axioms orientedTrace_inducesIsoH2

