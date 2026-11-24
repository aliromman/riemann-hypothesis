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

namespace Bl.MatrixMapSmul

theorem goal1 :
  ∀ {A : Type u_1} [inst : CommRing.{u_1} A] {d : Nat} (σ : RingHom.{u_1, u_1} A A) (a : A)
  (X : Matrix.{0, 0, u_1} (Fin d) (Fin d) A),
  Eq.{u_1 + 1}
    (Matrix.map.{u_1, u_1, 0, 0} (HSMul.hSMul.{u_1, u_1, u_1} a X) (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))
    (HSMul.hSMul.{u_1, u_1, u_1} (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ a)
      (Matrix.map.{u_1, u_1, 0, 0} X (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))) := by
  intro A _ d σ a X
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

end Bl.MatrixMapSmul
