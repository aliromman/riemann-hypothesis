module

public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.LocalToGlobal.Divisibility.BrJoint
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

namespace GlobalTheory.LvT.BuiltChain

theorem branching_ok : Formalism.MainNotions.PrimeDegreeVariant.Conclusion6 := Formalism.L2.DIV.BrJ.branching_interlacing_pairs

end GlobalTheory.LvT.BuiltChain
