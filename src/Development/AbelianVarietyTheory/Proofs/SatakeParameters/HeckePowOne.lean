module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

namespace GlobalTheory.WeightTwoHeckePower

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N M : ℕ}

abbrev sPow (X : GenModel gb N) (r : ℕ) : (GlobalTheory.KS.pow X.univ.A r).left ⟶ Sp R :=
  (GlobalTheory.KS.pow X.univ.A r).hom ≫ X.s

end GlobalTheory.WeightTwoHeckePower
