import ZInQKernel.Contrib.OneProof.HeightModelM.Rows
import ZInQKernel.OneProof.H.TailZ107
import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.SilvermanRankOne

/-!
# Fold check: `frozenTarget` with the two Gaudron–Rémond rows over the GR1 height

`OpenResearchLeaves79M` is the research bundle `HDec.HSyn.OpenResearchLeaves79` with the fields
`gaudronRemondSec9LowerAnSS` and `gaudronRemondThm14Printed` replaced by
`gaudronRemondSec9LowerGR1Weak : GaudronRemondSec9LowerGR1Weak` (the current field's strength;
the print `GaudronRemondSec9LowerGR1` implies it), `gaudronRemondThm14GR1 :
GaudronRemondThm14GR1` and the printed leaf `egaIV_9_7_7_OL : EGAIV_9_7_7_OL`: 17 fields instead
of 16, so the count goes up by one. `openResearchLeaves79_of_M` rebuilds the current bundle field
by field (`gaudronRemondSec9LowerAnSS_of_GR1Weak`, `gaudronRemondThm14Printed_of_GR1`), and
`frozenTargetM` is `ZInQ.OneProof.frozenTarget` over the new bundle, with the same proof term.
-/

namespace ZInQ.HeightModelM

/-- The research bundle with the two Gaudron–Rémond rows over the GR1 height and the EGA leaf. -/
structure OpenResearchLeaves79M : Prop where
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  afCharpolyDS965 : _root_.AfTateLam.AfCharpolyDS965
  modularHTCoeff : _root_.HTNewAssembly.ModularHTCoeff
  deligneCanonicalModelY3EveryPrint : _root_.Y3Hodge.DeligneCanonicalModelY3EveryPrint
  /-- GR1 Cor. 8.4, weakened to `-(3/2) g`, over the GR1 height
  (replaces `gaudronRemondSec9LowerAnSS`). -/
  gaudronRemondSec9LowerGR1Weak : GaudronRemondSec9LowerGR1Weak
  javanpeykarThm111An : _root_.JavanpeykarAnRetype.JavanpeykarThm111An
  y3FullThreeRepZ30 : _root_.Y3RouteA.Y3FullThreeRepZ30
  carayolThmAFrob : _root_.CarayolRefold.CarayolThmAFrob
  cmHeight62 : _root_.HDec.CMBranch.CMHeight62
  fowlerProp27PrintCanonical : _root_.HDec.CMBranch.FowlerBridges.FowlerProp27PrintCanonical
  cmjDegreePrint : _root_.HDec.CMBranch.CMjBridges.CMjDegreePrint
  silverbergZarhinThm34 : _root_.SZRaynaud.SilverbergZarhinThm34
  bergerSurveyF : _root_.HDec.PkgI4.PanDict.BergerSurveyF
  panThm104F : _root_.HDec.PkgI4.PanBergerRefereed.PanThm104F
  /-- Duke 163 Thm 1.4 over the GR1 height (replaces `gaudronRemondThm14Printed`). -/
  gaudronRemondThm14GR1 : GaudronRemondThm14GR1
  /-- EGA IV₃ (9.7.7)(ii) at `Spec 𝓞_L` (new printed leaf). -/
  egaIV_9_7_7_OL : EGAIV_9_7_7_OL

/-- The current research bundle from the new one, field by field. -/
theorem openResearchLeaves79_of_M (n : OpenResearchLeaves79M) :
    HDec.HSyn.OpenResearchLeaves79 where
  pazukiCor13Upper := n.pazukiCor13Upper
  dsThm966Printed := n.dsThm966Printed
  afCharpolyDS965 := n.afCharpolyDS965
  modularHTCoeff := n.modularHTCoeff
  deligneCanonicalModelY3EveryPrint := n.deligneCanonicalModelY3EveryPrint
  gaudronRemondSec9LowerAnSS :=
    gaudronRemondSec9LowerAnSS_of_GR1Weak n.egaIV_9_7_7_OL n.gaudronRemondSec9LowerGR1Weak
  javanpeykarThm111An := n.javanpeykarThm111An
  y3FullThreeRepZ30 := n.y3FullThreeRepZ30
  carayolThmAFrob := n.carayolThmAFrob
  cmHeight62 := n.cmHeight62
  fowlerProp27PrintCanonical := n.fowlerProp27PrintCanonical
  cmjDegreePrint := n.cmjDegreePrint
  silverbergZarhinThm34 := n.silverbergZarhinThm34
  bergerSurveyF := n.bergerSurveyF
  panThm104F := n.panThm104F
  gaudronRemondThm14Printed :=
    gaudronRemondThm14Printed_of_GR1 n.egaIV_9_7_7_OL n.gaudronRemondThm14GR1

/-- **Theorem 1.1 over the restated bundle**: `ZInQ.OneProof.frozenTarget` with the research
bundle `OpenResearchLeaves79M` (the two Gaudron–Rémond rows over the GR1 height, plus EGA IV₃
(9.7.7)); the proof term is `frozenTarget`'s with `r` passed through `openResearchLeaves79_of_M`. -/
theorem frozenTargetM
    (r : OpenResearchLeaves79M) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves30)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves)
    (hRank : ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open100 (openResearchLeaves79_of_M r) t l)
    (ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne hRC hCT
      (ZInQ.Manuscript.PoleS12.SilvermanRank.rankOne_of_aec hRank))

end ZInQ.HeightModelM
