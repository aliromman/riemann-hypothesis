module

public import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount
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

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

private theorem UpperTheory.ConvolutionTheory.G3.orbZero_avg {H : Type} [Group H] (u : H → ℂ) (hu : ∀ x, u x = 0) :
    GlobalTheory.BCT.avg u = 0 := by
  unfold GlobalTheory.BCT.avg
  rw [finsum_eq_zero_of_forall_eq_zero fun q => hu _, mul_zero]

theorem UpperTheory.ConvolutionTheory.G3.orbZero :
    UpperTheory.ConvolutionTheory.G3.OrbZero := by
  intro G _ _ θ K δ f hf
  unfold GlobalTheory.BCT.twOrb
  refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
  rw [UpperTheory.ConvolutionTheory.G3.orbZero_avg _ fun k => hf _ ⟨_, rfl⟩, mul_zero]
