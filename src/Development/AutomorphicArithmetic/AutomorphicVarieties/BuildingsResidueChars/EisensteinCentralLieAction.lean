module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Trzero
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

open UpperTheory.V.Sd.Eis

theorem UpperTheory.eisenstein_central_lie_action :
    UpperTheory.V.Sd.Eis.CentLie :=
  fun F _ _ _ _ _ ω hω φ hφ v => UpperTheory.V.Sd.Hm.trzero F ω hω φ hφ.cent v
