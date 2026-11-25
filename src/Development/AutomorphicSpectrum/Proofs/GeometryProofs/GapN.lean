module

public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual
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

namespace GlobalTheory.CompanionTheory.Ar.ExRefEff

def gapN {Ψ : Type} {N : ℕ} (ν : Ψ × Fin N → ℤ) : Option (Ψ × Fin N) → ℤ
  | none => 0
  | some p => ν p - if h : (p.2 : ℕ) + 1 < N then ν (p.1, ⟨p.2 + 1, h⟩) else 0

end GlobalTheory.CompanionTheory.Ar.ExRefEff
