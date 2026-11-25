module

public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
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

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

theorem UpperTheory.ConvolutionTheory.D.galExt :
    UpperTheory.ConvolutionTheory.D.GalExt := by
  intro F E k _ _ _ _ _ σ q h
  exact (UpperTheory.ConvolutionTheory.D.galBase F E k σ q h).2.2.2
