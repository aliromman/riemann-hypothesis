module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

section Fibres

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O))

def specialFibre : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))

def specialι : specialFibre f ⟶ Z := pullback.fst _ _

end Fibres

end

end GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
