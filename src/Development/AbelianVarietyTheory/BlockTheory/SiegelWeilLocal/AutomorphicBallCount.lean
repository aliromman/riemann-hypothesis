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

open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount

open Formalism.MainNotions.S GlobalTheory.Count

def ballSet (I : AutInst) (x : I.GA) (r : InfinitePlace I.F → ℝ) : Set I.GA :=
  {γ | γ ∈ I.GFset ∧ (x⁻¹ * γ * x).2 ∈ I.Kset ∧ ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ r v}

def bigA (I : AutInst) (x : I.GA) : ℝ :=
  (3 * Real.sqrt (I.n : ℝ) / (tau1 I x) ^ 2) ^ (2 * (I.n ^ 2 * I.f))

def AutBallCount : Prop :=
  ∀ (I : AutInst), 1 ≤ I.n → ∀ (x : I.GA) (r : InfinitePlace I.F → ℝ), (∀ v, 0 ≤ r v) →
    (ballSet I x r).Finite ∧
      ((ballSet I x r).ncard : ℝ) ≤ bigA I x * Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v)

end GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount
