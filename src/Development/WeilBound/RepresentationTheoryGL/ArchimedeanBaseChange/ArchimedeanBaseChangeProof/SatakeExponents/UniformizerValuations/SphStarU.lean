module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
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

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT

namespace PositivityTheory.Rg.BcB.F.Eig

def SphStarU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ) (w : Pl E) (σ : SmIrr (UL n w)),
  GlobalTheory.SmGL.IsUnitarisable σ.ρ → Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1 → ∀ h₁ h₂, IsHecke (KL n w) h₁ → IsHecke (KL n w) h₂ →
    twTr σ.ρ (KL n w) (KL n w) (lconv h₁ h₂) LinearMap.id =
      twTr σ.ρ (KL n w) (KL n w) h₁ LinearMap.id * twTr σ.ρ (KL n w) (KL n w) h₂ LinearMap.id ∧
    twTr σ.ρ (KL n w) (KL n w) (lstar h₁) LinearMap.id = starRingEnd ℂ (twTr σ.ρ (KL n w) (KL n w) h₁ LinearMap.id) ∧
    twTr σ.ρ (KL n w) (KL n w) ((KL n w : Set (UL n w)).indicator 1) LinearMap.id = 1

end PositivityTheory.Rg.BcB.F.Eig

end
