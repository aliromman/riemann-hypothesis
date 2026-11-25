module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
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
import Mathlib.Tactic.TypeStar

@[expose] public section

open Matrix

namespace GlobalTheory.UnitaryLieAlgebra

variable {n : Type*} [Fintype n]

def unitaryLie (J : Matrix n n ℂ) : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | Xᴴ * J + J * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  smul_mem' := by
    intro r X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX,
      smul_zero]

end GlobalTheory.UnitaryLieAlgebra
