module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
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

open Finset

noncomputable section

namespace GlobalTheory.WigSh

def wP {n : ℕ} (L : Fin (n + 1) → ℤ) (M : Fin n → ℤ) (l : Fin (n + 1)) : ℝ :=
  (∏ j, ((M j : ℝ) - 1 - (L l : ℝ))) / ∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ))

def wM {n : ℕ} (L : Fin (n + 1) → ℤ) (M : Fin n → ℤ) (l : Fin (n + 1)) : ℝ :=
  (∏ j, ((M j : ℝ) - (L l : ℝ))) / ∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ))

end GlobalTheory.WigSh
