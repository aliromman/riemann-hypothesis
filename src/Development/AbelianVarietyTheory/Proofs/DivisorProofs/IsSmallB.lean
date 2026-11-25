module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

def IsSmallB (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) (y : v.adicCompletion ℚ ⊗[ℚ] M) : Prop :=
  ∀ i, Valued.v ((Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i) < 1

end GlobalTheory.AdicSpan
