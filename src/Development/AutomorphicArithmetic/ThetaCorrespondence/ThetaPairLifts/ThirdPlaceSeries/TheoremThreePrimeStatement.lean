module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
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



section
noncomputable section
namespace Formalism.MainNotions.AdmissibleThreePrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
def Adm3PVariant (D : D7) : Prop := SumRepresentations.tieLab D ∧ _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D
def ThreePrimeTheoremStatement (D : D7) : Prop := _root_.Formalism.MainNotions.AdmissibleThreePrime.Adm3PVariant D → TheoremThreePrime D
end Formalism.MainNotions.AdmissibleThreePrime
end
end
