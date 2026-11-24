module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Sum
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

open Finset

namespace PositivityTheory.RgHe.Frame

variable {m : ℕ}

def pfR (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) (j : Fin m) : ℝ :=
  (∏ i, (d' j - d i)) / ∏ k ∈ univ.erase j, (d' j - d' k)

def pfX (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) : ℝ := ∑ i, d i - ∑ j, d' j

def above (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) (r : ℝ) : ℕ :=
  (univ.filter fun x : Fin (m + 1) ⊕ Fin m => r < Sum.elim d d' x).card

def pfD (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) (i : Fin (m + 1)) : ℝ :=
  (∏ k ∈ univ.erase i, (d i - d k)) / ∏ j, (d i - d' j)

end PositivityTheory.RgHe.Frame
