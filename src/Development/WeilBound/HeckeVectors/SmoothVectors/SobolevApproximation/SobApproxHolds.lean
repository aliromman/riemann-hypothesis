module

public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfSt
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfAs
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfAvg
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfBdd
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfChart
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfHaar
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfKFin
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfKer
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
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfA

@[expose] public section

namespace CompanionTheory.D.gk.HC

open Formalism.IndefR.Tow.SobPf

open scoped Matrix.Norms.Elementwise

theorem sobApprox_holds : SobApprox :=
  sobApprox_of haarExists_holds polyKernel_holds (avgSmooth_of sobChart_holds) avgKFin_holds
    (continuity_of_sobolev_chart sobChart_holds foldCont_holds) (foldBddK_of sobChart_holds)

end CompanionTheory.D.gk.HC
