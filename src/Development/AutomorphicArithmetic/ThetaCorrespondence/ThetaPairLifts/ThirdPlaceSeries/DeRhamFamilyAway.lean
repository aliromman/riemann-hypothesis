module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents
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
namespace Formalism.MainNotions.AdmissibleParameterJ
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual NumberField IsDedekindDomain
variable {D : D7}
section Sets
variable (D)
end Sets
section Emb
variable (D)
variable {D}
end Emb
section Stmt
variable (D)
variable {D} (L : SizeData₂ D)
end Stmt
section admitted
variable (D)
def DeRhamFamilyAwayAlt : Prop := ∀ i r, GoodR D.nd i r → _root_.UpperTheory.GalS.G2a D.nd D.naut i r
variable {D} (L : SizeData₂ D)
def AdmJAlt : Prop :=
  _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D ∧ CrysIffWD D.nd D.naut ∧ _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D ∧ AdmDict D ∧ AdmRead D ∧ AdmPar L
variable (D) in
def JumpClosed : Prop := ∀ L : SizeData₂ D, _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L → JumpConditions L
end admitted
end Formalism.MainNotions.AdmissibleParameterJ
end
end
