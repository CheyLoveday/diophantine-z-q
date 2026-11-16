import ZInQKernel.Contrib.OneProof.SGRDirectNVLocal
open IsLocalRing HDec
#check @Ideal.height_eq_zero_iff
#check @Ideal.under_ne_bot
#check @IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
#check @Ideal.IsPrime.eq_of_le_of_height_le
#check @Ideal.height_mono
#check @Ideal.height_le_of_le
#check @minimalPrimes_eq_bot
#check @Ideal.inertiaDegIn_eq_inertiaDeg
#check @Ideal.inertiaDeg
#check @IsIntegralClosure.MulSemiringAction
#check @IsGalois.card_aut_eq_finrank
#check @Algebra.isSeparable_tower_top_of_isSeparable
#check @IsIntegralClosure.isDedekindDomain
#check @Ideal.LiesOver.trans
example : True := by
  trivial
