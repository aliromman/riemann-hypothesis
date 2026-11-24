module

public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
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

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.UpqHaarRight

alias isMulRightInvariant := _root_.GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure

end GlobalTheory.UpqHaarRight
