module

import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Card
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GlobalTheory.CardFilterLt

theorem card_filter_val_lt : ∀ {n h : ℕ}, h ≤ n → Finset.card {m : Fin n | (↑m : ℕ) < h} = h :=
  fun hh => Fin.card_filter_val_lt.trans (min_eq_right hh)

end GlobalTheory.CardFilterLt
