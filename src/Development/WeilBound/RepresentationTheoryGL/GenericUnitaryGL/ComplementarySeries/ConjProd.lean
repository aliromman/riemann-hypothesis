module

import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.ConjProd
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
import Mathlib.Tactic.Linter.Style
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace PositivityTheory.RgGu.NR.ConjProd

def semiInv {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : X →ₛₗ[starRingEnd ℂ] Y) (hφ : Function.Bijective φ) : Y →ₛₗ[starRingEnd ℂ] X where
  toFun := Function.surjInv hφ.2
  map_add' a b := hφ.1 (by rw [map_add (f := _), Function.surjInv_eq hφ.2, Function.surjInv_eq hφ.2,
    Function.surjInv_eq hφ.2])
  map_smul' c y := hφ.1 (by
    rw [Function.surjInv_eq hφ.2, map_smulₛₗ, Function.surjInv_eq hφ.2]
    simp)

theorem semiInv_apply {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : X →ₛₗ[starRingEnd ℂ] Y) (hφ : Function.Bijective φ) (y : Y) : φ (semiInv φ hφ y) = y :=
  Function.surjInv_eq hφ.2 y

theorem semiInv_apply' {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : X →ₛₗ[starRingEnd ℂ] Y) (hφ : Function.Bijective φ) (x : X) : semiInv φ hφ (φ x) = x :=
  hφ.1 (semiInv_apply φ hφ (φ x))

end PositivityTheory.RgGu.NR.ConjProd

namespace PositivityTheory.RgGu.NR

theorem conjProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ConjProd k :=
  CompanionTheory.RgGu.NR.conjProd k

end PositivityTheory.RgGu.NR

end
