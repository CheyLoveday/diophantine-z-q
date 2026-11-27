import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal
import ZInQKernel.Contrib.OneProof.CasselsTatePairing
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent
import ZInQKernel.Contrib.OneProof.SilvermanRankOne
import ZInQKernel.Contrib.OneProof.DS965Reroute.Chain5

/-! # Headline check for ds965-reroute

* `researchLeaves77DS_ofLive`: the research bundle `OpenResearchLeaves77` (`TailZ103`, live when this
  check was written, off the live route since) gives `OpenResearchLeaves77DS` by field projections,
  except `bergerSurveyF`, which `PanBergerRefereed.bergerSurveyF_of_colmez` derives from `colmezThm01`
  (berger-restore). The new bundle has two fields fewer: `dsThm965AtPrimes` and `shimuraThm1Af`
  (m1-afshimura).
* `frozenTarget_without_ds965`: `ZInQ.OneProof.frozenTarget`'s body (`OneProof/Main.lean`)
  verbatim, with `HDec.HSyn.sixContactMin_of_open96` replaced by
  `HDec.HSyn.sixContactMin_of_open96_ds`, over `OpenResearchLeaves77DS`.
-/

namespace DS965Reroute

/-- `OpenResearchLeaves77` gives the new bundle field by field, except `bergerSurveyF`, which is derived
from `colmezThm01` (no field is proved here). -/
def researchLeaves77DS_ofLive (r : HDec.HSyn.OpenResearchLeaves77) :
    HDec.HSyn.OpenResearchLeaves77DS where
  pazukiCor13Upper := r.pazukiCor13Upper
  dsThm966Printed := r.dsThm966Printed
  afCharpolyDS965 := r.afCharpolyDS965
  modularHTCoeff := r.modularHTCoeff
  deligneCanonicalModelY3EveryPrint := r.deligneCanonicalModelY3EveryPrint
  gaudronRemondSec9LowerAnSS := r.gaudronRemondSec9LowerAnSS
  gaudronRemondThm14AnSS := r.gaudronRemondThm14AnSS
  javanpeykarThm111An := r.javanpeykarThm111An
  y3FullThreeRepZ30 := r.y3FullThreeRepZ30
  carayolThmAFrob := r.carayolThmAFrob
  cmHeight62 := r.cmHeight62
  fowlerProp27PrintCanonical := r.fowlerProp27PrintCanonical
  cmjDegreePrint := r.cmjDegreePrint
  silverbergZarhinThm34 := r.silverbergZarhinThm34
  bergerSurveyF := _root_.HDec.PkgI4.PanBergerRefereed.bergerSurveyF_of_colmez r.colmezThm01
  panThm104F := r.panThm104F

example : HDec.HSyn.OpenResearchLeaves77DS → HDec.HSyn.OpenTextbookLeaves18 →
    HDec.HSyn.OpenAddedLeaves28 → _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_open96_ds

/-- **Theorem 1.1 without `dsThm965AtPrimes`**: `frozenTarget` with the research bundle
`OpenResearchLeaves77DS` (`OpenResearchLeaves77` without `dsThm965AtPrimes` and `shimuraThm1Af`, with
`bergerSurveyF` for `colmezThm01`). -/
theorem frozenTarget_without_ds965
    (r : HDec.HSyn.OpenResearchLeaves77DS) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves28)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves)
    (hRank : ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne) :
    _root_.ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open96_ds r t l)
    (ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne hRC hCT
      (ZInQ.Manuscript.PoleS12.SilvermanRank.rankOne_of_aec hRank))

end DS965Reroute

#print axioms DS965Reroute.frozenTarget_without_ds965
#print axioms DS965Reroute.researchLeaves77DS_ofLive
#print axioms DS965Reroute.eigenformRepExistsG9_of_modularHT
#print axioms DS965Reroute.eigenformRepExists_of_modularHT
#print axioms DS965Reroute.eigenformHT_of_kato_mht
#print axioms HDec.PkgI4.PanDict.panBerger_of_F'
#print axioms HDec.PkgI4.PanDict.panBerger_of_F_mht
#print axioms HDec.HSyn.sixContactMin_of_open96_ds
