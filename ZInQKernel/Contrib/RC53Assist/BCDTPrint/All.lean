import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Statement
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Dictionary
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Literal
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Examples
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Cite

/-!
# Theorem A of Breuil–Conrad–Diamond–Taylor as printed: all modules

* `Statement.lean`: the PRINT `BCDTThmAPrinted` (Theorem A with condition (2)) over Mathlib's cusp
  forms on `Γ₁(N)` and the vendored Hecke operators.
* `Descent.lean`: `bcdtThmA_of_printed : BCDTThmAPrinted → PoleS12.BCDTThmA` (trivial nebentypus
  by the Hecke coefficient formula and Dirichlet's theorem).
* `Dictionary.lean`: the printed `T_p` formula, the printed cusp forms, `c_p = a_p c_1`, and the
  L-function equality as coefficient equality.
* `Literal.lean`: the same statement in the printed vocabulary, proved equivalent.
* `Examples.lean`: the discriminant is an eigenform in the printed sense (non-vacuity).
* `Cite.lean`: the printed statement in `PoleS12.kolyvaginRankOne_of_printed` and
  `PrintsAnalytic.modularNewform_of_printed`.
-/
