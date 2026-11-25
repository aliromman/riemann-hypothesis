module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneOfCompleteTwoNeZero
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

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.squaringOpenAtOne_of_complete_two_ne_zero : ∀ (K : Type) [NormedField K] [CompleteSpace K], (2 : K) ≠ 0 → SqOpen K := by
  first | exact @GlobalTheory.sqOpen_of_two_ne_zero
