module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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

noncomputable section

namespace GlobalTheory.MonoConj

def dualRep {Γ k : Type} [Group Γ] [CommRing k] {a : ℕ} (r : Γ →* GL (Fin a) k) : Γ →* GL (Fin a) k where
  toFun g := ⟨((r g⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose,
    ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose, by
      rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.transpose_one], by
      rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' g h := by
    apply Units.ext
    simp [mul_inv_rev, Matrix.transpose_mul]

theorem coe_dualRep {Γ k : Type} [Group Γ] [CommRing k] {a : ℕ} (r : Γ →* GL (Fin a) k) (g : Γ) :
    ((dualRep r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((r g⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose := rfl

end GlobalTheory.MonoConj

end
