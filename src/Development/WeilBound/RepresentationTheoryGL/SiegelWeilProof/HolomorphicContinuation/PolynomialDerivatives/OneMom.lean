module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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

namespace PositivityTheory.Rg.Sw.LC

def OneMom : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ p q : ℕ,
    MeasureTheory.Integrable (fun z : ℂ => z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))) ∧
    ∫ z : ℂ, z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) =
      if p = q then ((Real.pi * (p.factorial : ℝ) / c ^ (p + 1) : ℝ) : ℂ) else 0

end PositivityTheory.Rg.Sw.LC
