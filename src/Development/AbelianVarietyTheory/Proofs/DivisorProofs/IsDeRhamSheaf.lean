module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham

namespace GlobalTheory.DeRhamSheaf

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

abbrev onAff {V : T.Opens} (hV : IsAffineOpen V) : Over (Sp Γ(T, V)) :=
  (Over.pullback hV.fromSpec).obj A

instance {V : T.Opens} (hV : IsAffineOpen V) : GrpObj (onAff A hV) := Functor.grpObjObj

end GlobalTheory.DeRhamSheaf
