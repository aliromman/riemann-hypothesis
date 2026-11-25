module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
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
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace

namespace PositivityTheory.Rg.Tf.Core

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def PolyBd (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, ∀ (φ : L2 μ) (x : G1 K n), ‖rconv (Gam K n) μ a φ x‖ ≤ C * qht x ^ N * ‖φ‖

def CuspDecay (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n) : Prop :=
  ∀ N' : ℕ, ∃ C : ℝ, ∀ φ ∈ cuspidalL2 μ, ∀ x : G1 K n,
    ‖rconv (Gam K n) μ a φ x‖ ≤ C * (qht x ^ N')⁻¹ * ‖φ‖

end PositivityTheory.Rg.Tf.Core
