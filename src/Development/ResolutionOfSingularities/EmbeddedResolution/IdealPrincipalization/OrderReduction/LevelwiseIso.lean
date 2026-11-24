module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
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

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem BlowupSequenceData.iteratedStrictTransform_top {X : Scheme.{u}} (d : BlowupSequenceData X) (i : ℕ) :
    d.iteratedStrictTransform i ⊤ = ⊤ := by
  induction i with
  | zero =>
      rw [BlowupSequenceData.iteratedStrictTransform_zero]
      simp
  | succ i ih =>
      rw [BlowupSequenceData.iteratedStrictTransform_succ, ih, _root_.FunctorialResolution.EmbeddedResolution.strictTransform_top]

end FunctorialResolution.EmbeddedResolution

end
