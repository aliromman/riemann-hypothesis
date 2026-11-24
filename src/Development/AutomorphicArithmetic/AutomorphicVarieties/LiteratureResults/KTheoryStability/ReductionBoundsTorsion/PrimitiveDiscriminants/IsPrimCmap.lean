module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
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

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB

namespace LargePrimeDiscriminant

theorem isCyc_cmap (hC : SChain) {G H : Type} [Group G] [Group H] (f : G →* H) {m : ℕ}
    {z : Chn G (m + 1)} (hz : IsCyc z) : IsCyc (cmap f (m + 1) z) := by
  unfold IsCyc at hz ⊢
  rw [hC.2.1 G H f m z, hz, map_zero]

end LargePrimeDiscriminant

end PositivityTheory.KB

end
