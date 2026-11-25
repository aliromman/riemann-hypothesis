module

public import Formalism.WeaklyAdmissibleFiltrations.StatementTor
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
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

theorem le_of_growth {q a b C : ℕ} (hq : 2 ≤ q) (h : ∀ r : ℕ, q ^ (r * a) ≤ C * q ^ (r * b)) :
    a ≤ b := by
  by_contra hab
  have hba : b + 1 ≤ a := by omega
  have hq0 : 0 < q := by omega
  have h1 := h C
  have h2 : q ^ (C * (b + 1)) ≤ q ^ (C * a) :=
    Nat.pow_le_pow_right hq0 (Nat.mul_le_mul_left _ hba)
  have h3 : q ^ (C * b) * q ^ C ≤ q ^ (C * b) * C := by
    calc q ^ (C * b) * q ^ C = q ^ (C * (b + 1)) := by rw [Nat.mul_add, Nat.mul_one, pow_add]
      _ ≤ C * q ^ (C * b) := h2.trans h1
      _ = q ^ (C * b) * C := by ring
  have h4 : q ^ C ≤ C := Nat.le_of_mul_le_mul_left h3 (pow_pos hq0 _)
  have h5 : C < q ^ C := Nat.lt_pow_self (by omega)
  omega


end PositivityTheory.LocalTateOrthogonality.Bk
