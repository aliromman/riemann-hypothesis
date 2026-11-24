module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightWith
public import Formalism.LocalRingCardinality.DataParams
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

namespace GlobalTheory.CoreHt

open NumberField Formalism.BasicNotions Formalism.MainNotions

def HtRowsS {D : D7} (L : SizeData₂ D) (CY : ℝ) : Prop :=
  Nonempty (ParameterChoice' D L) ∧
  (Real.log D.host.rdE ≤ L.sc.L ∧ |L.logDerivativeAtOne| ≤ L.sc.L ∧ Real.log (4 * L.sc.x) ≤ L.sc.L) ∧
  (∀ i, Real.log (D.host.g i) ≤ CY * L.sc.L + 1) ∧
  (4 * (D.R.N D.R.m : ℝ) ^ 3 ≤ L.etaSz ∧ (D.R.t : ℝ) ≤ L.etaSz ∧
    (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n ∧ (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n ∧
    ∀ t, (L.bT t : ℝ) ≤ 2 * L.sc.b') ∧
  DelNat D ∧ ThickUp L

end GlobalTheory.CoreHt
