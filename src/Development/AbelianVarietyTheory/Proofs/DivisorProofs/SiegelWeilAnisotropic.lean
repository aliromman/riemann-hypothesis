module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
import Formalism.LocalRingCardinality.DataHost
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
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.ThetaInner

def LaurentConst (h : ℂ → ℂ) (s₀ c : ℂ) : Prop :=
  ∃ p : Polynomial ℂ, p.coeff 0 = 0 ∧ Tendsto (fun s => h s - p.eval (s - s₀)⁻¹) (𝓝[≠] s₀) (𝓝 c)


section Interface

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B)


variable {O}

end Interface

variable {D : D7}

section Towers

variable (T : ThetaX D)

end Towers

variable (Z : DivX D) (T : ThetaX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)


end GlobalTheory.ThetaInner

end
