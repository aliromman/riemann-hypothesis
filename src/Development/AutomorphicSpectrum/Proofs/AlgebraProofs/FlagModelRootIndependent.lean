module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitAlt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitBis
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelValueIndependent
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelRootIndep
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

namespace GlobalTheory.CompanionTheory.Ar.RootIndep

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.proof _root_.GlobalTheory.CompanionTheory.CommAlg.FlagModelValue.main

end GlobalTheory.CompanionTheory.Ar.RootIndep
