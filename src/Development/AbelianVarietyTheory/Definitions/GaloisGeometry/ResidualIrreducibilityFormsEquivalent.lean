module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
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

namespace GlobalTheory.NFacts

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem residualIrreducibility_forms_equivalent (D : D7) : SumRepresentations.adm6 D ↔ ResidualIrreducibleRankR D := Iff.rfl

end GlobalTheory.NFacts

end
