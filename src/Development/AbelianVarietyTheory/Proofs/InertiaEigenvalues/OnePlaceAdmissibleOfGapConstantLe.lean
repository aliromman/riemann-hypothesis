module

public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineInequalityDcrisFiniteConcreteRings
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineIneq

theorem one_place_admissible_of_gap_constant_le : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.LiftingTheory.adm22 D HW F := by
  intro D HW F l _ K LL
  exact (GlobalTheory.Per.FontaineBound.fontaineLe_of_tied l (D.loc l) (D.locA l) (D.locT l) K LL).1

end GlobalTheory.FontaineIneq
