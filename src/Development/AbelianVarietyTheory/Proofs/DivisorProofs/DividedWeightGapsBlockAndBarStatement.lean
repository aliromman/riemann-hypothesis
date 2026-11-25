module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar
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

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

theorem _root_.GlobalTheory.T.dividedWeight_gaps_block_and_bar : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (((b : ℕ) ≠ W.p → (W.T : ℤ) + W.Dd + 2 + 2 * N ≤ W.u1 τ a - W.u1 τ b) ∧ ((b : ℕ) = W.p → W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) ∧ W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b - 3 * N)) ∧ ((b : ℕ) ≠ W.p → W.kc ≤ (a : ℕ) → W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b))) := by
  first | exact @GlobalTheory.MeanTop.divided_gaps
