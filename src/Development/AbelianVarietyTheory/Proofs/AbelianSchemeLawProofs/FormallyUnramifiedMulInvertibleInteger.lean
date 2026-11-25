module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem formallyUnramified_mulA (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ)
    (hn : IsUnit (n : Γ(S, ⊤))) : FormallyUnramified (mulA G n).left := by
  have h : mulN G n = mulA G n :=
    (Category.id_comp _).symm.trans (MulUnramified.comp_mulN G (𝟙 G) n)
  rw [← h]
  exact formallyUnramified_mulN S G n hn

end GlobalTheory
