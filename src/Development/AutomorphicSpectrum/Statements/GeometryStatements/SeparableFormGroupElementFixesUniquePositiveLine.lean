module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFFCurve
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

namespace GlobalTheory.CompanionTheory.Ar.Conj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Top

def RootLineDeRhamModel : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (j p : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (_ : DRTie M j p H), p.Prime → 2 < p → 1 ≤ j → j < N →
    ∀ mu : Wt Ψ N, Dominant mu → NefThreshold j p mu → M.NefAt p mu 0

end GlobalTheory.CompanionTheory.Ar.Conj
