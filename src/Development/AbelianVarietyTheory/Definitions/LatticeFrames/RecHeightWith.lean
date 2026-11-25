module

public import Formalism.LocalRingCardinality.DataParams₂
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne

@[expose] public section

noncomputable section

namespace GlobalTheory.CoreHt

open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Col2

def DelNat (D : D7) : Prop := ∃ n : ℕ, D.s.Del = n

def ThickUp {D : D7} (L : SizeData₂ D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces → wj D j τ ≤ L.sc.b + L.etaSz + 1

end GlobalTheory.CoreHt
