module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetRationalProductOfLocalLevels
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct

theorem GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU (E := E) (n := n))), IsOpen (L : Set (finU (E := E) (n := n))) → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (L : Set (finU (E := E) (n := n)))) := by
  intro E _ _ _ n L hL
  exact GlobalTheory.BCT.ClassFinLev.finite_doubleCoset_of_isOpen L hL
