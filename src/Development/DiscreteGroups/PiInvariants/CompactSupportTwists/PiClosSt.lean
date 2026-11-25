module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
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

open NumberField MeasureTheory
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

def PiClosureInv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
  ∀ (D : Dom E n 0) (π : CuspSub E n), ThetaFix π → ∀ (ι : Type) [Fintype ι] (ψ : ι → Sm E n) (u : ι → ℝ → ℂ)
  (z : H E n 0) (f : Hs (ι := ι) D), (∀ i, ψ i ∈ π.V ∧ Continuous (u i) ∧ HasCompactSupport (u i)) →
  (∀ i, (f i : H E n 0 → ℂ) =ᵐ[D.ν] fun x => (ψ i).1 (x * z).1 * u i (ldet (x * z))) → f ∈ piSp D π ι

end DiscreteGroups.T1.G

end
