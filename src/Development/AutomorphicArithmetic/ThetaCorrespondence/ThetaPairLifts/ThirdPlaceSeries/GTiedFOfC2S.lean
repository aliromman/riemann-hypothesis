module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
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



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
theorem gTiedF_of_C2S_alt {eps : ℝ} (Fm : FamP eps) (h : _root_.Formalism.L2.SecondChernLinkedClass Fm) : G.GroupCompatibilityFamily Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i hx1 => ?_⟩
  obtain ⟨T⟩ := hx0 x hx1 ((le_max_left _ _).trans hx) i
  exact ⟨T.g⟩
end Formalism.L2
end
end
