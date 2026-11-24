module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.MinusculeCentralEigen
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.ConvergenceEntriesGeneralLinearHolds
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

@[expose] public section

namespace PositivityTheory.jumpWindows

theorem cuspidalMultiplicityOne : GlobalTheory.Published.CuspidalMultiplicityOne := cuspidal_multiplicity_one PositivityTheory.JacquetShalikaLocal.minuscule_eigenvalue PositivityTheory.JacquetShalikaLocal.satake_eigenvalue_formula

end PositivityTheory.jumpWindows
