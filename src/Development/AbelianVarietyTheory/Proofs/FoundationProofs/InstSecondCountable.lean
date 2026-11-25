module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.BlockOrderedSquareIntegrable
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.HolDS

variable {p q : ℕ}

instance t2Space_cuspAdeles (T : GrpData p q) : T2Space T.G := T.emb.t2Space

instance instSecondCountable (T : GrpData p q) : SecondCountableTopology T.G := by
  haveI : SecondCountableTopology (Mat p q) := inferInstanceAs (SecondCountableTopology (Ix p q → Ix p q → ℂ))
  haveI : SecondCountableTopology (Mat p q)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Ix p q) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  exact T.emb.secondCountableTopology

instance instLocallyCompact (T : GrpData p q) : LocallyCompactSpace T.G := by
  haveI : LocallyCompactSpace (Mat p q) := inferInstanceAs (LocallyCompactSpace (Ix p q → Ix p q → ℂ))
  exact (GlobalTheory.RealPar.SqInt.isClosedEmbedding_emb T).locallyCompactSpace

end GlobalTheory.HolDS

end
