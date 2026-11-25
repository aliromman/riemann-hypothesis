module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct

theorem _root_.GlobalTheory.T.divisorsAt_inv_dualLabel_and_stabilizer_mul : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V), e * e = e → ϖ ≠ 0 → DivAt V e ϖ d α → DivAt V e ϖ (dualLab d) α⁻¹ ∧ ∀ a ∈ KsphC V ∅, ∀ b ∈ KsphC V ∅, DivAt V e ϖ d (a * α * b) := by
  first | exact @GlobalTheory.DivDual.divAt_inv_and_mul
