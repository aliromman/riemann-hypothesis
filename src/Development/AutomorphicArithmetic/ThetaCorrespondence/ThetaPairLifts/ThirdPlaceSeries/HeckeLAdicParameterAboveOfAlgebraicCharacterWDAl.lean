module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeLAdicParameterAbove
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
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
namespace GlobalTheory
theorem heckeLAdicParameterAbove_of_algebraicCharacterWD_alt (H : GlobalTheory.Published.AlgebraicCharacterWD) :
    _root_.GlobalTheory.Published.HeckeLAdicParameterAboveAlt := by
  intro E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ hχ hμ hL w A h O _ _ _ Bw hj ξ hξ rc hrc
  first | (have hOpn := UpperTheory.One.M.opn _ (hrc); obtain ⟨a, ha, ε, L⟩ := hOpn)
  rw [H E Ω l P AI hT ι art hart χ n μ hχ hμ hL w A h O Bw hj ξ hξ a ha]
  exact (L.one ξ hξ.1).symm
end GlobalTheory
end
