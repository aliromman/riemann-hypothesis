module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.EqOfInner
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

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E
open scoped Real

namespace PositivityTheory.ThKR

def LocalLift : Prop :=
  ∀ (l : Type) [Fintype l] [DecidableEq l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ), X ∈ LieAlgebra.Symplectic.sp l ℝ →
    ∃ (ε : ℝ) (V : ℝ → Sch l →L[ℂ] Sch l) (W : ℝ → Sch l →L[ℂ] Sch l) (c : ℂ), 0 < ε ∧ (∀ f, V 0 f = f) ∧
      (∀ t, |t| < ε → (∀ f, V t (W t f) = f) ∧ (∀ f, W t (V t f) = f) ∧
        Impl (fun w => NormedSpace.exp (t • X) *ᵥ w) (V t).toLinearMap) ∧
      (∀ t, |t| < ε → ∀ f (lam : Sch l →L[ℂ] ℂ), DifferentiableAt ℝ (fun u => lam (V u f)) t) ∧
      ∀ f (lam : Sch l →L[ℂ] ℂ), HasDerivAt (fun u => lam (V u f)) (lam (quad X f + c • f)) 0

end PositivityTheory.ThKR
