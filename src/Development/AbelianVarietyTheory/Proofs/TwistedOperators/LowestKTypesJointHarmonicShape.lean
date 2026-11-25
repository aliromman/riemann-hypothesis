module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitaryS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
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
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory

theorem lowestKTypes_jointShape : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → (IsParam (lamA al be ga de) ∧ IsParam (lamA' t al be ga de) ∧ IsParam (lamM' t al be ga de)) ∧ JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamA' t al be ga de)) ∧ JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamM' t al be ga de)) := by
  intro t al be ga de h
  obtain ⟨hA, hpA, hpA', -, -⟩ := _root_.GlobalTheory.LowestTypes.lowest_types t al be ga de h
  obtain ⟨hM, hpM', -, -⟩ := _root_.GlobalTheory.TypesMirror.types_mirror t al be ga de h
  exact ⟨⟨hpA, hpA', hpM'⟩, hA, hM⟩

end GlobalTheory
