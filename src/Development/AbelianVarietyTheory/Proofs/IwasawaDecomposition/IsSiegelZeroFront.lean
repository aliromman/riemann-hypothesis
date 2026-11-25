module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linter.Style
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

open Matrix

namespace GlobalTheory.RedTh

structure IsSiegel {n : ℕ} (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) : Prop where

  nonneg : ∀ i, 0 ≤ d i

  step : ∀ p q : Fin n, (q : ℕ) = p + 1 → d p ≤ 4 * d q

  diag : ∀ i, u i i = 1

  lower : ∀ i j, j < i → u i j = 0

  upper : ∀ i j, i < j → |u i j| ≤ 1 / 2

def gram {n : ℕ} (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := uᵀ * diagonal d * u

section Act

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {n : ℕ}

def actMat (b : Module.Basis (Fin n) ℤ X) : O →+* Matrix (Fin n) (Fin n) ℤ :=
  ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom).comp (Module.toModuleEnd ℤ X)

theorem actMat_apply (b : Module.Basis (Fin n) ℤ X) (c : O) (i j : Fin n) : actMat b c i j = b.repr (c • b j) i := by
  show LinearMap.toMatrixAlgEquiv b (Module.toModuleEnd ℤ X c) i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply]
  rfl

end Act

end GlobalTheory.RedTh
