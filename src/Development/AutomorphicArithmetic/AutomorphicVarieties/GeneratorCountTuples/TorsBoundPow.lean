module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
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

open NumberField

namespace UpperTheory.V.K

abbrev HGL (L : Type) [Field L] [NumberField L] (N m : ℕ) : Type :=
  groupHomology (Rep.trivial ℤ (GL (Fin N) (𝓞 L)) ℤ) m

abbrev torsHGL (L : Type) [Field L] [NumberField L] (N m : ℕ) : AddSubgroup (HGL L N m) :=
  AddCommGroup.torsion (HGL L N m)

end UpperTheory.V.K

end
