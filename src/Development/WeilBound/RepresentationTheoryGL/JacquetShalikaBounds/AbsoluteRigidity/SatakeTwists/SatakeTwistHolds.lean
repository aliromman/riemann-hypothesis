module

public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
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

namespace PositivityTheory.RgJS

open GlobalTheory.CuspRep

theorem satake_twist_holds : SatTw := by
  intro E _ _ _ m π χ w B hχ h
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

end PositivityTheory.RgJS
