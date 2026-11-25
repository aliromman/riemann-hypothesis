module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.NormIteratedFDerivIdLeOneAdd
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

namespace PositivityTheory.ThKF0

def SchwartzDq : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (a : V) (L : V →L[ℝ] ℝ) (f : SchwartzMap V ℂ)
    (G : ℝ → SchwartzMap V ℂ), (∀ t x, G t x = Lib.hl a L t f x) → ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ,
      HasDerivAt (fun t => T (G t)) (T (Lib.dop a L f)) 0

end PositivityTheory.ThKF0
