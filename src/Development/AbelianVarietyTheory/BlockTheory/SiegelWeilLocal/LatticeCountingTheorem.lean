module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem

open NumberField Formalism.MainNotions.S

def CountingTheorem : Prop :=
  ∀ Cg : ℝ, ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    GlobalTheory.Count.CountHyp B Cg n₀ d p q b →
      FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧
        |(B.D : ℝ) - GlobalTheory.Count.mainTerm B d| ≤
          Real.exp (-(1 / 16 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) *
            GlobalTheory.Count.mainTerm B d

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem
