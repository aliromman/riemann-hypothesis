module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForward
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.NumericalSegre
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

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.FieldNumbers

open GroundTheory.Heights₂.Heights.FieldNumbers GroundTheory.Heights₂.Heights.NumbersDVR

theorem projectionFormulaDegree :
    GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{0} :=
  ProjectionFormulaDegree.of_divPushForward
    (DivPushForward.proof ContractRelDimLe.proof DivPushForwardLocalZero)

end GlobalTheory.CompanionTheory.FieldNumbers
