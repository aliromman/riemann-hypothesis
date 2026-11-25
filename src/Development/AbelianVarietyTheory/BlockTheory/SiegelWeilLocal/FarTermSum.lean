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

open MeasureTheory NumberField
open scoped ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate

open Formalism.MainNotions.S GlobalTheory.Count

variable (B : RowsAut)

def farSet (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | γ ∈ B.I.GFset ∧ ¬ IsNear B d (epN B) x γ}

def farSum (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : ℝ≥0∞ :=
  ∑' γ : farSet B d x, ‖phe B d (x⁻¹ * γ.1 * x)‖ₑ

def moderate (q : ℕ) (b : ℝ) : Set B.I.GA :=
  {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x}

def FarModerate : Prop :=
  ∀ Cg : ℝ, 0 ≤ Cg → ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    1 ≤ q → CountHyp B Cg n₀ d p q b →
      ∫⁻ x in moderate B q b, farSum B d x ∂(B.I.muA B.μf) ≤
        ENNReal.ofReal (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d)

end GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate
