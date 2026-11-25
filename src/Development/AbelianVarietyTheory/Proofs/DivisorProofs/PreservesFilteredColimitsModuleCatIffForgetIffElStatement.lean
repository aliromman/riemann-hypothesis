module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsModuleCatIffForgetIffEl
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements : ∀ (Λ : Type 1) [Ring Λ] (N : CommRingCat.{0} ⥤ ModuleCat.{1} Λ), (PreservesFilteredColimitsOfSize.{0, 0} N ↔ PreservesFilteredColimitsOfSize.{0, 0} (N ⋙ forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})) ∧ (PreservesFilteredColimitsOfSize.{0, 0} N ↔ ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ x : N.obj c.pt, ∃ j y, (N.map (c.ι.app j)).hom y = x) ∧ ∀ j (y : N.obj (D.obj j)), (N.map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (N.map (D.map f)).hom y = 0) := by
  first | (exact @GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements)
