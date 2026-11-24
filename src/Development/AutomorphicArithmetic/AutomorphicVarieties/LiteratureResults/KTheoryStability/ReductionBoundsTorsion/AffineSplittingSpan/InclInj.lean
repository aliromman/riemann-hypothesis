module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

@[expose] public section

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.SplitAffineSpectral

def EvCob : Prop :=
  ∀ (G : Type) [Group G] (j : ℕ) (e : (Fin (j + 1) → G) → ℝ), Inv (MonoidHom.id G) e →
    ∀ z : Chn G (j + 1), IsCyc z → ev (MonoidHom.id G) (dC e) 1 z = 0

namespace GluingInclusion

set_option linter.unusedSectionVars false

variable (L : Type) [Field L] [NumberField L] (n r : ℕ)

end GluingInclusion

end PositivityTheory.KB.SplitAffineSpectral

end
