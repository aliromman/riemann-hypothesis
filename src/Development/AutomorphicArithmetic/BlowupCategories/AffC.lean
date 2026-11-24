module

public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.Blow

def affD : CommRingCat.{0} ⥤ Type where
  obj A := A
  map f := TypeCat.ofHom f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

def affC : Act where
  D := affD
  G := (Functor.const _).obj (GrpCat.of PUnit.{1})
  smul _ _ x := x
  one_smul _ _ := rfl
  mul_smul _ _ _ _ := rfl
  nat _ _ _ := rfl

end UpperTheory.Blow
end
