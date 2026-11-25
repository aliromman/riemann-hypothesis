module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.TowerRallisLemma
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.CoreHolds
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

namespace UpperTheory.Gal.KunnethLefschetz.Top
open CrystallineSemistableComparison

theorem diagEt3_holds : CrystallineSemistableComparison.Onto.DiagEt3 := core_holds.diagEt3

theorem etSide_sm_holds (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    EtSide (Model.Sm (l := l) (K := K)) := core_holds.etSide_sm l K

theorem etFin_holds : CrystallineSemistableComparison.Onto.EtFin := core_holds.etFin

end UpperTheory.Gal.KunnethLefschetz.Top
