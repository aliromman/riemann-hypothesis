module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Strong
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExSummand
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
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

theorem UpperTheory.ConvolutionTheory.Dp.atInj :
    UpperTheory.ConvolutionTheory.Dp.AtInj := by
  intro E _ _ _ n μ _ V V' hV hV' S hS t h h'
  obtain ⟨π, hπ, -⟩ := exCusp E n μ V hV
  obtain ⟨π', hπ', -⟩ := exCusp E n μ V' hV'
  have e : π = π' := by
    refine GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.strongMultOneC E n π π' ?_)
    filter_upwards [hS.eventually_cofinite_notMem] with w hw
    obtain ⟨B, hB, h1⟩ := (sSatIff E n μ π V hπ w _).1 (h w hw)
    obtain ⟨B', hB', h2⟩ := (sSatIff E n μ π' V' hπ' w _).1 (h' w hw)
    obtain rfl : B = B' := Multiset.map_injective Units.val_injective (hB.symm.trans hB')
    exact ⟨_, h1, h2⟩
  subst e
  rw [((exSummand E n μ π V).1 hπ).2, ((exSummand E n μ π V').1 hπ').2]
