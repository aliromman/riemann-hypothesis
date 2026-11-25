module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecT
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SOfStar
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SPairs
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
namespace UpperTheory.GalS
theorem bridgeStar_alt : GlobalTheory.Published.GelfandKazhdanDual → (_root_.UpperTheory.One.M.Row → _root_.UpperTheory.GalS.CarUAlt) ∧ (_root_.UpperTheory.GalS.PairUAlt → _root_.UpperTheory.GalS.CuspUAlt) :=
  fun hGK => ⟨_root_.UpperTheory.GalS.ofDual_star_alt hGK, _root_.UpperTheory.GalS.cusp_of_pair_alt hGK⟩
end UpperTheory.GalS
end
