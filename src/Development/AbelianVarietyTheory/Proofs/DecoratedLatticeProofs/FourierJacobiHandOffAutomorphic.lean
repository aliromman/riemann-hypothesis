module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedThetaKernelContinuousAndRationallyInvarianStatement
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
open GlobalTheory.Unf

namespace GlobalTheory

theorem handFBLaw : ∀ D : D7, HandFBLaw D := by
  intro D
  unfold HandFBLaw
  intro ψ σ J B s vL Y Ξ hY hΞ

  obtain ⟨hc, hl, hr⟩ := GlobalTheory.T.pairedThetaKernel_continuous_and_rationally_invariant D ψ σ J B s vL Y Ξ hY hΞ
  refine ⟨fun γ hγ g => ?_, ?_⟩
  ·
    simp only [handFB, hr γ hγ]
  ·
    exact (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D J.W₀ J.cpt J.v0 (GA D B.A) (pairKer s vL Y Ξ) hc hl).2.1

end GlobalTheory
