module

public import Mathlib.Data.Nat.Notation
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

namespace GlobalTheory

def chainEdge (k : ℕ) {r : ℕ} (i j : Fin r) : Prop := j.val = i.val + 1 ∧ i.val + 1 ≠ k

instance (k : ℕ) {r : ℕ} : DecidableRel (chainEdge k (r := r)) := fun i j =>
  inferInstanceAs (Decidable (j.val = i.val + 1 ∧ i.val + 1 ≠ k))

end GlobalTheory
