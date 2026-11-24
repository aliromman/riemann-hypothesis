module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
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

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def eps (i : N.Loc) : G H.E N.Om →* (N.O i)ˣ :=
  (Units.map (algebraMap ℤ_[N.l i] (N.O i)).toMonoidHom).comp
    (cycZ (F := H.E) (Ω := N.Om) (N.l i))

end GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
