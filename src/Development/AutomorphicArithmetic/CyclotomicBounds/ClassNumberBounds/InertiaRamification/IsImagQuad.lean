module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
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

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ}

def IsImagQuad (ψ : DirichletCharacter ℂ N) (d : ℕ) : Prop :=
  ψ ^ 2 = 1 ∧ ψ.Odd ∧ ψ.conductor = d

end KStar.Ram
