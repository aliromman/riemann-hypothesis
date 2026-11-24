module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
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
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions
open scoped Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

section Theta
variable {P : Type} [Fintype P]

end Theta

section Schur
variable {T : Type} [Fintype T] {n₀ : ℕ}

end Schur

def hookProd (n : ℕ) (ν : ℕ → ℕ) : ℕ :=
  ∏ r ∈ Finset.range n, ∏ c ∈ Finset.range (ν r),
    ((ν r - c - 1) + ((Finset.Ioo r n).filter (fun r' => c < ν r')).card + 1)

variable (D : D7)

end GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

end
