module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
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

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open GlobalTheory.BCT

theorem hintSph : HintSph := by
  intro G _ K u hu
  have hK : rStab u ⊓ K = K := inf_eq_right.mpr fun k hk x => hu k hk x
  unfold hint
  rw [hK, Subgroup.relIndex_self]
  simp

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
