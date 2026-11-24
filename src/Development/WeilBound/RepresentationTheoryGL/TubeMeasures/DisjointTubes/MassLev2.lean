module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
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

open NumberField

noncomputable section

namespace MainStatements.Tam

def massB (E : Type) [Field E] [NumberField E] (r : ℕ) : ℝ :=
  (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (r : ℝ) ^ 4 *
    (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^ (3 * Module.finrank ℚ E * r ^ 2)

def massLev2 (E : Type) [Field E] [NumberField E] (r M : ℕ) : ℝ :=
  (M : ℝ) ^ (Module.finrank ℚ E * r ^ 2) * 15 ^ (Module.finrank ℚ E * r ^ 2) * massB E r

end MainStatements.Tam

end
