module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorCosetIndicator
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

@[expose] public section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum Lifts)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.CosetSB

theorem cosetInd_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k]
    (f : Module.Dual 𝓀[k] (Red L)), cosetInd q L f ∈ SB (n → k) := by
  intro k _ _ _ _ n _ _ q L _ f
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  by_cases hex : ∃ F : n → k, Lifts L F f
  · obtain ⟨F, hF⟩ := hex
    have e : cosetInd q L f = fun η => dualInd L (η - q.inv • F) := by
      funext η
      rw [← GlobalTheory.FinPl.CosetPairing.cosetInd_add q hF (η - q.inv • F), sub_add_cancel]
    rw [e]
    exact GlobalTheory.FinPl.Comm.comp_mem_SB (GlobalTheory.FinPl.Comm.dualInd_mem L) (s := fun η => η + q.inv • F)
      (by fun_prop) (by fun_prop) fun η => sub_add_cancel η _
  · have e : cosetInd q L f = 0 := by
      classical
      funext η
      unfold cosetInd
      rw [ite_eq_right fun ⟨F, hF, _⟩ => hex ⟨F, hF⟩]
      rfl
    rw [e]
    exact (SB (n → k)).zero_mem

end GlobalTheory.FinPl.CosetSB
