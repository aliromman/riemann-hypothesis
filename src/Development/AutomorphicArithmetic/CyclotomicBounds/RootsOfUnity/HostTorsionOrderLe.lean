module

public import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.Monomial
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

open NumberField Formalism.BasicNotions

namespace UpperTheory.Mu

theorem host_torsionOrder_le {R : Ranks} (H : Host R) : Units.torsionOrder H.E ≤ 8 * R.f ^ 2 := by
  have h := _root_.Formalism.L2.SG.NGCut.TorsionTotientBound.torsionOrder_le H.E
  rw [H.finrank_cmField] at h
  have hn : R.f = 2 * R.ord := rfl
  rw [hn]
  calc Units.torsionOrder H.E ≤ 2 * (4 * R.ord) ^ 2 := h
    _ = 8 * (2 * R.ord) ^ 2 := by ring

theorem one_le_f (R : Ranks) : 1 ≤ R.f := by
  have h := R.ord_pos
  show 1 ≤ 2 * R.ord
  omega

end UpperTheory.Mu
