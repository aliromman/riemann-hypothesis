module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
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

namespace GlobalTheory.CompanionTheory.LocCompareHalves

open PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.UnitaryBC GlobalTheory.BCT

theorem locCompareOf : PositivityTheory.Rg.BcB.G8.Fin.LocCompareOf := by
  intro hI hS hC E _ _ _ hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw
  by_cases hs : IsSplitAt w
  · exact hS hC E hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw hs
  · exact hI hC E hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw hs

end GlobalTheory.CompanionTheory.LocCompareHalves
