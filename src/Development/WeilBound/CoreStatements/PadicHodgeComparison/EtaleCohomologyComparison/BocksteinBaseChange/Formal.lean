module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductGradedCommRingAxiomsHold
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyBijectiveOfSupportBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvariance
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.Inputs
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

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

theorem formalIn : FormalIn :=
  ⟨GlobalTheory.EtC.quasiIso_hypercohomology_bijective', GlobalTheory.EtC.a6nat_holds, GlobalTheory.EtC.a6ring_holds, GlobalTheory.EtC.coefSeq_exact, GlobalTheory.EtC.a8,
    GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero, GlobalTheory.EtC.a10,
    E.etIn⟩

end CrystallineSemistableComparison
