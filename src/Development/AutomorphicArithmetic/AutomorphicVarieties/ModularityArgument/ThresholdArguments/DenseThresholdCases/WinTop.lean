module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcross
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FlagLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormAbsPowUnif
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinUpDown
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdThruL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAIsoTwOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAUpDownOf
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section




section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N UpperTheory.V.Af UpperTheory.GalN.V
namespace UpperTheory.V.Z.Win
theorem aIsoTw_alt : _root_.UpperTheory.V.Z.Win.AIsoTwAlt := _root_.UpperTheory.V.Z.Win.aIsoTwOf_alt flagLaws ImaginaryQuadraticEtaCharacter.winTw
theorem aUpDown_alt : _root_.UpperTheory.V.Z.Win.AUpDownAlt := fun P =>
  _root_.UpperTheory.V.Z.Win.aUpDownOf_alt weakOfAtt flagLaws thruF (_root_.UpperTheory.V.Z.Ord.thruL_alt P.toClassicalTheorems plainRec) ImaginaryQuadraticEtaCharacter.winUpDown ImaginaryQuadraticEtaCharacter.winOf P
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} [IsAlgClosure F Ω]
theorem WitA.witness_twist_algebraic_character [IsCMField F] (P : _root_.UpperTheory.V.Af.Hypotheses') {μ : G F Ω →* (Qbar l)ˣ} (hμ : IsAlgChar ι μ)
    (h : WitA ι r) : WitA ι (Af.tw r μ) := (_root_.UpperTheory.V.Z.Win.aIsoTw_alt P F Ω l ι n r h).2 μ hμ
end UpperTheory.V.Z.Win
end
