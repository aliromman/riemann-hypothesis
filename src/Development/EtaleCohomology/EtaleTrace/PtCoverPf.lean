module

public import Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfLocalTwist
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

open CategoryTheory AlgebraicGeometry

namespace LateralTheory.EtaleTrace

theorem PtCover_of : PtCover := by
  intro k _ _ T hT
  obtain ⟨Y, g, hg, y, hy⟩ := (Scheme.geometricFiber k).jointly_surjective T hT (𝟙 (S k))
  have hy' : y ≫ g = 𝟙 (S k) := hy
  have := T.downward_closed hg y
  rwa [hy'] at this

end LateralTheory.EtaleTrace
