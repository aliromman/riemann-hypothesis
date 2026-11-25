module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace PositivityTheory.Rg.BcB.FC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

abbrev Fam (E : Type) [Field E] [NumberField E] (a b : ℕ) : Type := ∀ w : Pl E, GLw a w × GLw b w → ℂ

end PositivityTheory.Rg.BcB.FC

end
