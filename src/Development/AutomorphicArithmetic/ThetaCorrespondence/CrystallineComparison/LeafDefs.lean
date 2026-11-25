module

public import Development.WeilBound.CoreStatements.PeriodRingComparison.PadicPeriodAlgebraMaps.CPAlgebraMapPadic
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

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

def iotaP : ACris.ACris ℂ_[l] l →+* Formalism.Per6.BdRp l := ACris.iota ℂ_[l] l

def jOC : Reformulated.AutPerF.Acris l (Cmp6.OC l) →+* Reformulated.AutPerF.BdRPlus l (Cmp6.OC l) :=
  ((Cmp6.cP l).symm.toRingHom.comp (iotaP l)).comp (Cmp6.cA l).toRingHom

end Formalism.BasicNotions.CmpTie.Incl
