module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ThruBad
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

theorem UpperTheory.V.Z.Win.Birth.awTw :
    UpperTheory.V.Z.Win.Birth.AwTw := by
  intro F Ω _ _ _ _ _ _ l _ n hn ι r κ hκ haut hW
  obtain ⟨_, art, χ, a, hart, -, hL⟩ := hκ
  obtain ⟨π, hreg, hatt⟩ := haut
  obtain ⟨t, ht⟩ := hW π hreg hatt
  obtain ⟨b, hb⟩ := UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winTw F χ
  exact UpperTheory.V.Z.Win.Birth.awOne F Ω l n hn ι _ (π.twist χ)
    (UpperTheory.V.Af.Cq.attTwist F Ω l ι n r π hatt art χ a κ hart hL)
    ⟨t + b, fun v => hb n (by omega) π t v (ht v)⟩
