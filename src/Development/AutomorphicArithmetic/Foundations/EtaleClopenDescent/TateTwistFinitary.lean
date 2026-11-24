module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorIsFinitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistRingFunctorPreservesFilteredColimitsStatement
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem UpperTheory.Cb.tateTwist_finitary :
    ∀ (q : ℕ) (i : ℤ), Finitary (R := ZMod q) (tw q i) := by
  intro q i
  exact _root_.GlobalTheory.ofRings_finitary (ZMod q) (twF q i) (_root_.GlobalTheory.EtC.TwistFiltered.twF_preservesFilteredColimits q i)
