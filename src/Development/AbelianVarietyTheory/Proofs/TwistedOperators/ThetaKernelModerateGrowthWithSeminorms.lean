module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix

namespace GlobalTheory.KernelSeminorm

theorem thetaGrowth_onObjects : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D :=
  fun D => GlobalTheory.KernelSeminorm.thetaGrowth D

end GlobalTheory.KernelSeminorm
