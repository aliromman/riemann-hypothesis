module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
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

namespace GlobalTheory.CompanionTheory.HeckeEnd

open PositivityTheory.Rg.BcB.F.Tail.PExp

theorem hkE_fin : HkEFin := by
  intro G V _ _ _ ρ K f hf v
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.hkE PositivityTheory.Rg.BcB.F.Tail.PExp.hkS
  rw [finsum_eq_sum_of_support_subset (s := hf.toFinset),
    finsum_eq_sum_of_support_subset (s := hf.toFinset), LinearMap.sum_apply]
  · rfl
  all_goals
    intro q hq
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h
    rw [Function.mem_support] at hq
    exact hq (by simp [h])

end GlobalTheory.CompanionTheory.HeckeEnd
