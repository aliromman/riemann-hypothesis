module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.HodgeTateFromSandwich
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.StmtPhi
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

noncomputable section

open AlgebraicGeometry

namespace CrystallineSemistableComparison.Out

def CstSmooth : Prop := SmoothModelCrystalline ∧ DeRhamComparisonSmooth ∧ CrysPhi

def EtSideS : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  EtSide (Model.Sm (l := l) (K := K))

end CrystallineSemistableComparison.Out
