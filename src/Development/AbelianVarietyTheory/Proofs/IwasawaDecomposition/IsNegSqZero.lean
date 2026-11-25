module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
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

noncomputable section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.PointFormSign

def domGram (m r : ℕ) (x : Fin m → Fin r → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ((1 - Matrix.of x * (Matrix.of x)ᴴ)⁻¹)ᵀ

def IsNegSq {E : Type*} [AddCommGroup E] [Module ℂ E] {m : ℕ} (F : E → E → Matrix (Fin m) (Fin m) ℂ) (r : ℕ) : Prop :=
  ∃ (S : Matrix (Fin m) (Fin m) ℂ) (T : E →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ), IsUnit S.det ∧
    ∀ ξ η, F ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S

def sqPoly {n m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ a, ∑ b, C ((T (coordVec a) * (T (coordVec b))ᴴ) i j) * X (a, b)

end GlobalTheory.PointFormSign
