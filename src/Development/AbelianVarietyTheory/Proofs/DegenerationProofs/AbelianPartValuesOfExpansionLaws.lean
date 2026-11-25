module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.ThetaInValues

theorem brUth_of_laws : Laws → BrUthSt := fun hL _ _ _ _ _ _ _ _ _ _ _ ν =>
  ⟨fun _ _ _ _ hb hb' => weilIs_weil ν hL.globalFns hb hb', fun _ hm hF _ _ hb =>
    ⟨isThetaPt_uth ν hL.globalFns hm hF hb, isCoordPt_uth ν hL.globalFns hm hF hb⟩⟩

end GlobalTheory.ThetaInValues
