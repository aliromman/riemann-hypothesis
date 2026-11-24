module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatUnit
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SatIff
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TsphVec
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

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.sSatIff :
    UpperTheory.ConvolutionTheory.Dp.SSatIff := by
  intro E _ _ _ n μ _ π V h w B
  constructor
  · intro hB
    obtain ⟨B', rfl⟩ := (sSatUnit E n μ w V B hB).1
    exact ⟨B', rfl, (satIff E n μ π V h w B').2 ((tsphVec E n μ w V h.summand B').2 hB)⟩
  · rintro ⟨B', rfl, hB⟩
    exact (tsphVec E n μ w V h.summand B').1 ((satIff E n μ π V h w B').1 hB)
