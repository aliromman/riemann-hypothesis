module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArithKleiman
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PtsIntegralCurveConst
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

namespace PositivityTheory.MbHsUse

open GroundTheory.Heights₂.Heights.HilbertSamuel

def HSUse : Prop :=
  ArithKleiman.Statement ∧ G7.Statement ∧ ArithmeticVolumeNef.Statement

theorem HSUse.g7 (h : HSUse) : G7.Statement := h.2.1

theorem HSUse.g7p (h : HSUse) : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticHilbertSamuelUpperBound := h.2.2

theorem HSUse.z1 (h : HSUse) : ReciprocityTheory.ChartRestriction.G.Geo.SuccessiveMinimaLowerBound :=
  G5.proof' h.1 CurvePointsFinite.proof

end PositivityTheory.MbHsUse

namespace GlobalTheory.CompanionTheory.Ar.Giv

end GlobalTheory.CompanionTheory.Ar.Giv

namespace GlobalTheory.CompanionTheory.Ar.Small

end GlobalTheory.CompanionTheory.Ar.Small
