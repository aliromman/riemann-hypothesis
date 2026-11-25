module

public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
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

open UpperTheory.ConvolutionTheory.R

theorem UpperTheory.ConvolutionTheory.R.liftSum :
    LiftSum := by
  intro K M _ _ _ _ _ _ _ _ _ ι _ κ _ n m π P h
  have h' := Filter.eventually_all.2 h
  refine h'.mono fun w hw f hf => ?_
  choose B hB C hC e using fun i => hw i f hf
  refine ⟨∑ i, B i, ⟨B, hB, rfl⟩, fun a => C a.1 a.2, fun a => hC a.1 a.2, ?_⟩
  rw [Fintype.sum_sigma]
  have : (∑ i, B i).map (· ^ f) = ∑ i, (B i).map (· ^ f) :=
    map_sum (Multiset.mapAddMonoidHom (· ^ f)) B Finset.univ
  rw [this]
  exact Finset.sum_congr rfl fun i _ => e i
