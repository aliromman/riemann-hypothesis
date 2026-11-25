module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ToInhPartialProd
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

namespace UpperTheory.V.ZK

theorem sPrism : SPrism := by
  intro A _ G _ k m z
  obtain ⟨y, rfl⟩ := toInh_surjective A (m + 1) z
  rw [prism_toInh, bd_toInh, bd_toInh, prism_toInh, conj_toInh, ← map_add (f := _), ← map_sub, hbd_hprism]

end UpperTheory.V.ZK
