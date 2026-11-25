module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective

@[expose] public section

open GlobalTheory.ColPeriod

namespace GlobalTheory.ColPeriod

theorem heckeUnit : GlobalTheory.ColPeriod.HeckeUnit :=
  fun _ _ _ _ _ _ _ _ hX hPr hμ _ _ _ _ hw hP x _ hk => GlobalTheory.CharVal.mu_unit hX hPr hμ x hk hP hw

end GlobalTheory.ColPeriod
