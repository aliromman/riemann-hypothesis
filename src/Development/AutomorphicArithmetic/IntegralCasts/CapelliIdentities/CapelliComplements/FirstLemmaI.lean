module

public import Mathlib.LinearAlgebra.Matrix.Defs
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

universe u_1

namespace Bl.MatrixMapSub

theorem goal1 {A : Type u_1} [CommRing A] {d : ℕ} (σ : A →+* A)
    (X Y : Matrix (Fin d) (Fin d) A) :
    (X - Y).map σ = X.map σ - Y.map σ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]

end Bl.MatrixMapSub
