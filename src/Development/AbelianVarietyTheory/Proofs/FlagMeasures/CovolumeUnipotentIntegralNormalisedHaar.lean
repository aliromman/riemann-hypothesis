module

import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.CovarianceFormula

@[expose] public section

open scoped Classical ENNReal
open MeasureTheory

noncomputable section

namespace GlobalTheory.CovNFormulaPf

theorem main : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula :=
  Formalism.MainStatements.RowRest.covariance_formula

end GlobalTheory.CovNFormulaPf
