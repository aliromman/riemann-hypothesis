module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PadMHerm
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

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.BlockEvaluationBounds

open BlockInvariants

def WOneOdd : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N q : ℕ) (x : Pat L q), Odd q → ncyc x.1 = 1 →
    ∃ (r : ℝ) (w : InfinitePlace L), AT (N := N) x =
      r • (AT (N := N) ((finRotate q, fun _ => w, false) : Pat L q) +
        AT (N := N) ((finRotate q, fun _ => w, true) : Pat L q))

def WRot : Prop := ∀ q : ℕ, 0 < q → ncyc (finRotate q) = 1

end PositivityTheory.KB.BlockEvaluationBounds

end
