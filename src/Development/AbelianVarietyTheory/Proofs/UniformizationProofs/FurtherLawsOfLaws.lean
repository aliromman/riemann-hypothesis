module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws3
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws5
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsSixthOfUnifUniq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniformisationLawsOfBaseChangeLaws
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem furtherLaws_of_laws :
    Laws → DVR.TwistBaseChangeStatement → Laws3 ∧ Laws4 ∧ Laws5 ∧ Laws6 :=
  fun h ht =>
    ⟨laws3, uniformisationLaws_of_baseChange_laws h.polBaseChange h.globalFns h.secBaseChange ht,
      laws5 h.globalFns h.secBaseChange,
      lawsSixth_of_unifUniq h.globalFns h.secBaseChange h.ample⟩

end GlobalTheory
