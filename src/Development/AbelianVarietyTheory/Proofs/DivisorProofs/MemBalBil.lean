module

public import Mathlib.LinearAlgebra.BilinearMap
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

noncomputable section

namespace GlobalTheory.BalRank

variable {O : Type} [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X]

def balBil : Submodule ℤ (LinearMap.BilinForm ℤ X) where
  carrier := {β | ∀ (a : O) y z, β (a • y) z = β y (bar a • z)}
  add_mem' := by
    rintro β β' h k a y z
    simp only [LinearMap.add_apply, h a y z, k a y z]
  zero_mem' := by simp
  smul_mem' := by
    rintro n β h a y z
    simp only [LinearMap.smul_apply, h a y z]

variable {bar X}

end GlobalTheory.BalRank
